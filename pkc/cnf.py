# Representation of CNF

import subprocess
import datetime

import readwrite
import ddnnf
import pog
import os

sequenceNumber = 10 * 1000 * 1000
root = None
addedFiles = []

# Global statistics
satCalls = 0
d4Calls = 0
satTime = 0.0
d4Time = 0.0


def nextSequence():
    global sequenceNumber
    sequenceNumber += 1
    return sequenceNumber
    
def setRoot(cnfName):
    global root
    if root is None:
        fields = cnfName.split(".")
        fields = fields[:-1]
        root = ".".join(fields)

def addFile(name):
    global addedFiles
    addedFiles.append(name)

def removeFiles():
    global addedFiles
    for fname in addedFiles:
        try:
            os.remove(fname)
        except:
            pass
    addedFiles = []

def tmpName(extension):
    global addedFiles
    lroot = "pog-process" if root is None else root
    name = "%s-xxxx-%d.%s" % (lroot, nextSequence(), extension)
    addFile(name)
    return name

def cleanFiles():
    for fname in addedFiles:
        try:
            os.remove(fname)
        except:
            pass

# Run BCP on clause list to create reduced list of clauses
def bcp(clauseList):
    uset = set([])
    clist = []
    for clause in clauseList:
        if len(clause) == 0:
            return [[]]
        elif len(clause) == 1:
            uset.add(clause[0])
        else:
            clist.append(clause)
    # Keep running
    go = True
    while go:
        go = False
        # Unit propagation
        nclist = []
        for clause in clist:
            tautology = False
            nclause = []
            for lit in clause:
                if lit in uset:
                    tautology = True
                    break
                elif -lit not in uset:
                    nclause.append(lit)
            if tautology:
                continue
            elif len(nclause) == 0:
                # Conflict
                return [[]]
            elif len(nclause) == 1:
                go = True
                uset.add(nclause[0])
            else:
                nclist.append(nclause)
        clist = nclist
    return [[lit] for lit in uset] + clist
        

def runD4(cnfName, nnfName):
    global d4Calls, d4Time
    d4Calls += 1
    start = datetime.datetime.now()
    cmd = ["d4", cnfName, "-dDNNF", "-out=%s" % nnfName]
    proc = subprocess.run(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    d4Time += seconds
    if proc.returncode != 0:
        sys.stdout.write("D4 dump:\n")
        sys.stdout.write(str(proc.stdout))
        raise ProjectionException("Running D4 on file %s gave return code %d" % (cnfName, proc.returncode))


# Represent CNF formula in packed form
# Final packed object is a single tuple
class PackedCnf:
    # Entire set of clauses represented as tuple
    # First element is number of input variables
    # Then come Unit literals ordered by absolute value
    # Then come clauses are ordered by their hashes,
    # consisting of [nvar] + literals + [0] + (clause + [0])*
    tup = ([])

    # When used as iterator
    # Position in tuple
    index = 0   
    # Number of zeros seen
    zcount = 0

    # Lazy calculations
    length = None
    hash = None

    def __init__(self, nvar):
        self.tup = tuple([nvar])
        self.index = 1
        self.zcount = 0
        self.length = None
        self.hash = None

    def nvar(self):
        return self.tup[0]

    # Iterator
    def __iter__(self):
        self.index = 1
        self.zcount = 0
        return self

    def __next__(self):
        if self.index >= len(self.tup):
            raise StopIteration
        clause = []
        while self.index < len(self.tup):
            val = self.tup[self.index]
            self.index += 1
            if val == 0:
                self.zcount += 1
                if self.zcount == 1 and self.index == len(self.tup):
                    raise StopIteration
                elif self.zcount > 1:
                    break
            else:
                clause.append(val)
                if self.zcount == 0:
                    break
        return clause

    # Get representation
    def object(self):
        return self.tup

    def isTautology(self):
        return len(self.tup) == 2

    def isNull(self):
        return len(self.tup) == 3 and self.tup[1] == 0

    def load(self, clauseList, runBcp = True):
        if runBcp:
            clauseList = bcp(clauseList)
        lset = set([])
        # Pair of (hash, clause)
        plist = []
        for clause in clauseList:
            # Special case.  If encounter empty clause, then entire representation changes
            if len(clause) == 0:
                self.tup = (self.nvar(), 0, 0)
                return
            if len(clause) == 1:
                lit = clause[0]
                if -lit in lset:
                    # Conflicting unit literals detected
                    self.tup = (self.nvar(), 0, 0)
                    return
                lset.add(lit)
            else:
                t = tuple(sorted(clause, key=lambda lit: abs(lit)))
                h = hash(t)
                plist.append((h,t))
        vlist = [self.nvar()]
        # Sort
        vlist += sorted(list(lset), key = lambda lit: abs(lit))
        # Terminate unit literals
        vlist.append(0)
        plist.sort(key = lambda p: p[0])
        # Concatenate clauses onto literals
        # Removing duplicates along the way
        lastClause = None
        for p in plist:
            clause = p[1]
            if lastClause is None or lastClause != clause:
                vlist += list(clause) + [0]
                lastClause = clause
        self.tup = tuple(vlist)

    # Export clausal representation
    def export(self):
        clauseList = []
        for clause in self:
            clauseList.append(clause)
        return clauseList

    # Return new tuple with some literals assigned and some variables ignored, and some clauses ignored
    # Run BCP on reduced clauses
    def reduce(self, assignedLiterals = None, ignoredVariables = None, partitionVariables = None):
        if assignedLiterals is None:
            assignedLiterals = set([])
        if ignoredVariables is None:
            ignoredVariables = set([])
        clist = []
        for clause in self:
            tautology = False
            nclause = []
            for clit in clause:
                if clit in assignedLiterals:
                    tautology = True
                    break
                elif -clit in assignedLiterals:
                    continue
                elif abs(clit) in ignoredVariables:
                    continue
                elif partitionVariables is not None and abs(clit) not in partitionVariables:
                    tautology = True
                    break
                else:
                    nclause.append(clit)
            if not tautology:
                clist.append(nclause)
        p = PackedCnf(self.nvar())
        p.load(clist)
        return p
                         
    def write(self, cnfName, showVariables = None, verbLevel = 1):
        if showVariables is not None:
            showVariables = showVariables & self.variables()
            if len(showVariables):
                showVariables = None
        cwriter = readwrite.CnfWriter(self.nvar(), fname=cnfName, verbLevel = verbLevel)
        if showVariables is not None:
            cwriter.doHeaderComment("t pmc")
        for clause in self:
            cwriter.doClause(clause)
        if showVariables is not None:
            slist = [str(v) for v in sorted(showVariables)]
            cwriter.doComment("p show %s 0" % " ".join(slist))
        cwriter.finish()

    # Handle simple POG generation.  Assume not null or tautolgy
    def makeSimplePog(self, verbLevel = 1):
        # Make sure clauses are partitioned
        vset = set([])
        for val in self.tup[1:]:
            if val == 0:
                continue
            var = abs(val)
            if var in vset:
                return None
            vset.add(var)
        print("Making pog in cnf.  %d variables" % self.nvar())
        pg = pog.Pog(self.nvar(), verbLevel)        
        # Build two-level representation:
        children = []
        for clause in self:
            if len(clause) == 1:
                # Unit clause
                children.append(clause[0])
            else:
                # Use DeMorgan's Laws
                pchildren = [-lit for lit in clause]
                nnode = pg.addProduct(pchildren)
                children.append(-nnode)
        root = pg.addProduct(children)
        pg.setRoot(root)
        return pg


    # Generate POG representation
    def makePog(self, verbLevel = 1, trySimple = True):
        if trySimple:
            pog = self.makeSimplePog(verbLevel)
            if pog is not None:
                return pog
        cnfName = tmpName("cnf")
        self.write(cnfName, verbLevel = verbLevel)
        nnfName = readwrite.changeExtension(cnfName, "nnf")
        addFile(nnfName)
        runD4(cnfName, nnfName)
        try:
            nfile = open(nnfName, 'r')
        except:
            raise ProjectionException("Couldn't open NNF file %s" % nnfName)
        dag = ddnnf.Nnf(verbLevel)
        d4reader = ddnnf.D4Reader(dag)
        if not d4reader.read(nfile) or not d4reader.build():
            raise PogException("Couldn't process NNF file %s" % nnfName)
        pg = dag.makePog(self.nvar())
        if verbLevel >= 2: 
            print("GEN: File %s.  Input NNF DAG has %d inputs, %d nodes --> %d POG nodes" % (
                nnfName, dag.inputCount, dag.realNodeCount, pg.nodeCount()))
        return pg

    def __len__(self):
        if self.length is None:
            n = 0
            for clause in self:
                n += 1
            self.length = n
        return self.length

    def __hash__(self):
        if self.hash is None:
            self.hash = hash(self.tup)
        return self.hash

    def __eq__(self, other):
        return self.tup == other.tup

    def literals(self):
        return set([val for val in self.tup[1:] if val != 0])

    def variables(self):
        return set([abs(val) for val in self.tup[1:] if val != 0])

    def pureLiterals(self):
        lits = self.literals()
        plits = []
        for v in self.variables():
            if -v not in lits:
                plits.append(v)
            elif v not in lits:
                plits.append(-v)
        return set(plits)

    def isSat(self):
        global satCalls, satTime

        if self.isNull():
            return False
        if self.isTautology():
            return True
        vset = self.variables()
        # Test if all literals are pure
        pset = set([abs(lit) for lit in self.pureLiterals()])
        if pset == vset:
            return True
        start = datetime.datetime.now()
        cnfName = tmpName("cnf")
        self.write(cnfName)
        cmd = ["cadical", "-q", cnfName]
        proc = subprocess.run(cmd, shell=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        satCalls += 1
        delta = datetime.datetime.now() - start
        seconds = delta.seconds + 1e-6 * delta.microseconds
        satTime += seconds
        return proc.returncode == 10

    def __str__(self):
        return str(self.tup)
