# Perform projection operations

import sys
import subprocess

import readwrite
import pog
import ddnnf

sequenceNumber = 10 * 1000 * 1000
root = None


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

def tmpName(extension):
    lroot = "pog-process" if root is None else root
    return "%s-xxxx-%d.%s" % (lroot, nextSequence(), extension)

class ProjectionException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Projection Exception: " + str(self.value)

# Mapping from CNF files to POGs
class PogCache:

    entries = {}

    def __init__(self):
        self.entries = {}
    
    def signature(self, clauseList):
        return tuple(sorted([hash(clause) for clause in clauseList]))

    def insert(self, clauseList, pog):
        self.entries[self.signature(clauseList)] = pog

    def find(self, clauseList):
        sig = self.signature(clauseList)
        if sig in self.entries:
            return self.entries[sig]
        else:
            return None

pcache = PogCache()

class ClauseManager:

    contextLiterals = set([])
    ignoreVariables = set([])
    nvar = 0
    clauses = []
    verbLevel = 0

    def __init__(self, nvar, clauses, verbLevel=1):
        self.nvar = nvar
        self.clauses = clauses
        self.verbLevel = verbLevel
        self.contextLiterals = set([])
        self.ignoreLits = set([])


    def setContext(self, contextLits, ignoreVars):
        self.contextLiterals = contextLits
        self.ignoreVariables = ignoreVars

    def reduceClause(self, lits, varSet):
        nlits = []
        lits = readwrite.cleanClause(lits)
        if lits == readwrite.tautologyId:
            return lits
        for lit in lits:
            if abs(lit) in self.ignoreVariables:
                continue
            if lit in self.contextLiterals:
                return readwrite.tautologyId
            if -lit in self.contextLiterals:
                continue
            nlits.append(lit)
            varSet.add(abs(lit))
        tup = tuple(nlits)
        return tup

    def reduce(self):
        varSet = set([])
        clauseSet = set([])
        clauseList = []
        for clause in self.clauses:
            nclause = self.reduceClause(clause, varSet)
            if nclause == readwrite.tautologyId:
                continue
            if nclause in clauseSet:
                continue
            clauseList.append(nclause)
            clauseSet.add(nclause)
        return clauseList, varSet

    def store(self, fname, clauseList, showVariables):
        cwriter = readwrite.CnfWriter(self.nvar, fname, self.verbLevel)
        cwriter.doHeaderComment("t pmc")
        if self.verbLevel >= 2:
            cwriter.doComment("Reduction of %d clauses to %d" % (len(self.clauses), len(clauseList)))
        slist = [str(lit) for lit in sorted(self.contextLiterals, key = lambda lit : abs(lit))]
        cwriter.doComment("Context literals: %s" % (" ".join(slist)))
        slist = [str(v) for v in sorted(self.ignoreVariables)]
        cwriter.doComment("Ignored variables: %s" % (" ".join(slist)))
        for clause in clauseList:
            cwriter.doClause(clause)
        slist = [str(v) for v in sorted(showVariables)]
        cwriter.doComment("p show %s 0" % " ".join(slist))
        cwriter.finish()

    def generate(self, fname, contextLiterals, ignoreVariables, showVariables):
        self.setContext(contextLiterals, ignoreVariables)
        clauseList, varSet = self.reduce()
        nshowVariables = varSet & showVariables
        self.store(fname, clauseList, nshowVariables)
        if self.verbLevel >= 2:
            print("GEN: File %s: %d original clauses --> %d reduced clauses" % (fname, len(self.clauses), len(clauseList)))


def runD4(cnfName, nnfName):
    cmd = ["d4", cnfName, "-dDNNF", "-out=%s" % nnfName]
    proc = subprocess.run(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if proc.returncode != 0:
        sys.stdout.write("D4 dump:\n")
        sys.stdout.write(str(proc.stdout))
        raise ProjectionException("Running D4 on file %s gave return code %d" % (cnfName, proc.returncode))

def isSat(cnfName):
    cmd = ["cadical", "-q", cnfName]
    proc = subprocess.run(cmd, shell=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return proc.returncode != 20
    

def cnf2pog(cnfName, nnfName, verbLevel):
    try:
        creader = readwrite.CnfReader(cnfName, verbLevel = verbLevel)
    except Exception as ex:
        raise ProjectionException("ERROR in CNF File: %s" % str(ex))
    if verbLevel >= 2:
        print("GEN: CNF file %s has %d variables and %d clauses" % (cnfName, creader.nvar, len(creader.clauses)))
    runD4(cnfName, nnfName)
    try:
        nfile = open(nnfName, 'r')
    except:
        raise ProjectionException("Couldn't open NNF file %s" % nnfName)
    dag = ddnnf.Nnf(verbLevel)
    d4reader = ddnnf.D4Reader(dag)
    if not d4reader.read(nfile) or not d4reader.build():
        raise PogException("Couldn't process NNF file %s" % nnfName)
    if verbLevel >= 2: 
       print("GEN: Input NNF DAG has %d inputs, %d nodes" % (dag.inputCount, dag.nodeCount()))
    pg = dag.makePog(creader.clauses)
    return pg

class Projector:
    pog = None
    showVariables = None
    cmgr = None
    verbLevel = 1
    rootName = None

    def __init__(self, cnfName, verbLevel = 1):
        creader = readwrite.CnfReader(cnfName, verbLevel)
        cfields = cnfName.split(".")[:-1]
        self.rootName = ".".join(cfields)
        self.showVariables = creader.showVariables
        if verbLevel >= 2:
            slist = [str(v) for v in sorted(self.showVariables)]
            print("GEN: Show variables: {%s}" % ", ".join(slist))
        self.verbLevel = verbLevel
        setRoot(cnfName)
        self.cmgr = ClauseManager(creader.nvar, creader.clauses, verbLevel)
        nnfName = readwrite.changeExtension(cnfName, "nnf")
        self.pog = cnf2pog(cnfName, nnfName, verbLevel)


    def write(self, fname):
        self.pog.write(fname)

    def traverseProduct(self, lit, contextLiterals):
        ref = self.pog.getRef(lit)
        node = ref.node
        if not ref.phase:
            raise ProjectionException("Can't traverse negated node %s" % str(ref))
        contextAddedLits = []
        nlits = []
        for cref in node.children:
            clit = cref.literal()
            if self.pog.isNode(clit):
                nclit = self.traverse(clit, contextLiterals)
                nlits.append(nclit)
            else:
                contextLiterals.add(clit)
                contextAddedLits.append(clit)
                if abs(clit) in self.showVariables:
                    nlits.append(clit)
        nchildren = [self.pog.getRef(lit) for lit in nlits]
        nref = self.pog.addProduct(nchildren)
        nlit = nref.literal()
        for lit in contextAddedLits:
            contextLiterals.remove(lit)
        return nlit

    def traverseSum(self, lit, contextLiterals):
        ref = self.pog.getRef(lit)
        node = ref.node
        if not ref.phase:
            raise ProjectionException("Can't traverse negated node %s" % str(ref))
        nlits = [self.traverse(c.literal(), contextLiterals) for c in node.children]
        nchildren = [self.pog.getRef(lit) for lit in nlits]
        dvar = node.findDecisionVariable()
        if dvar is None:
            raise ProjectionException("Can't find decision variable for node %s" % str(ref))
        nref = None
        if dvar not in self.showVariables:
            if self.verbLevel >= 3:
                print("  Decision variable = %d" % dvar)
            cnfName = tmpName("cnf")
            ignoreVariables = set([dvar])
            self.cmgr.generate(cnfName, contextLiterals, ignoreVariables, self.showVariables)
            if isSat(cnfName):
                xpog = cnf2ppog(cnfName, self.verbLevel)
                xref = self.pog.integrate(xpog)
                mref = self.pog.addSum([nchildren[0].negate(), xref])
                nref = self.pog.addSum([mref.negate(), nchildren[1]])
                if self.verbLevel >= 3:
                    print("   Traversing %s.  Integrated exclusionary term from CNF file %s" % (str(ref), cnfName))
            elif self.verbLevel >= 3:
                print("  Traversing %s.  CNF file %s unsatisfiable" % (str(ref), cnfName))
        if nref is None:
            nref = self.pog.addSum(nchildren)
        nlit = nref.literal()
        return nlit

    # Given literal, replace by result of projection
    def traverse(self, lit, contextLiterals):
        nlit = lit
        if self.verbLevel >= 3:
            sclist = [str(lit) for lit in sorted(contextLiterals, key = lambda lit : abs(lit))]
            print("Traversing %s.  Context = {%s}" % (str(self.pog.getRef(lit)), ", ".join(sclist)))
        if self.pog.isNode(lit):
            node = self.pog.getRef(lit).node
            if node.ntype == pog.NodeType.product:
                nlit = self.traverseProduct(lit, contextLiterals)
            else:
                nlit = self.traverseSum(lit, contextLiterals)
        elif abs(lit) in self.showVariables:
            nlit = lit
        else:
            nlit = readwrite.tautologyId
        if self.verbLevel >= 3:
            print("Traversing %s yields %s" % (str(self.pog.getRef(lit)), str(self.pog.getRef(nlit))))
        return nlit
                
    def run(self):
        contextLiterals = set([])
        if self.verbLevel >= 2:
            print("GEN: Initial POG:")
            self.pog.summarize()
        if self.verbLevel >= 3:
            self.pog.show()
        nroot = self.traverse(self.pog.rootLiteral, contextLiterals)
        if self.verbLevel >= 2:
            print("GEN: Changed root literal from %d to %d" % (self.pog.rootLiteral, nroot))
        self.pog.setRoot(nroot)
        self.pog.compress()
        if self.verbLevel >= 2:
            print("GEN: Projected POG:")
            self.pog.summarize()
        
def cnf2ppog(cnfName, verbLevel):
    creader = readwrite.CnfReader(cnfName, verbLevel, check = False)
    clauseList = readwrite.cleanClauses(creader.clauses, check=False)
    pog = pcache.find(clauseList)
    if pog is None:
        pr = Projector(cnfName, verbLevel)
        pr.run()
        pog = pr.pog
        pcache.insert(clauseList, pog)
        if verbLevel >= 2:
            print("Pcache miss.  %d clauses --> %d POG nodes" % (len(clauseList), len(pog.nodes)))
    elif verbLevel >= 2:
            print("Pcache hit.  %d clauses --> %d POG nodes" % (len(clauseList), len(pog.nodes)))
    return pog

