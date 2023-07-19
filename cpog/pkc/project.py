# Perform projection operations

import sys
import subprocess

import readwrite
import pog
import ddnnf


class ProjectionException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Projection Exception: " + str(self.value)


class ClauseManager:

    contextLiterals = set([])
    ignoreLiterals = set([])
    nvar = 0
    clauses = []
    verbLevel = 0

    def __init__(self, nvar, clauses, verbLevel=1):
        self.nvar = nvar
        self.clauses = clauses
        self.verbLevel = verbLevel
        self.contextLiterals = set([])
        self.ignoreLits = set([])


    def setContext(self, contextLits, ignoreLits):
        self.contextLiterals = contextLits
        self.ignoreLiterals = ignoreLits

    def reduceClause(self, lits):
        nlits = []
        lits = readwrite.cleanClause(lits)
        if lits == readwrite.tautologyId:
            return lits
        for lit in lits:
            if lit in self.ignoreLiterals:
                continue
            if lit in self.contextLiterals:
                return readwrite.tautologyId
            if -lit in self.contextLiterals:
                continue
            nlits.append(lit)
        tup = tuple(nlits)
        return tup

    def reduce(self):
        clauseSet = set([])
        clauseList = []
        for clause in self.clauses:
            nclause = self.reduceClause(clause)
            if nclause == readwrite.tautologyId:
                continue
            if nclause in clauseSet:
                continue
            clauseList.append(nclause)
            clauseSet.add(nclause)
        return clauseList

    def store(self, fname, clauseList):
        cwriter = readwrite.CnfWriter(self.nvar, fname, self.verbLevel)
        if self.verbLevel >= 2:
            cwriter.doComment("Reduction of %d clauses to %d" % (len(self.clauses), len(clauseList)))
        slist = [str(lit) for lit in sorted(self.contextLiterals, key = lambda lit : abs(lit))]
        cwriter.doComment("Context literals: %s" % (" ".join(slist)))
        slist = [str(lit) for lit in sorted(self.ignoreLiterals)]
        cwriter.doComment("Ignored literals: %s" % (" ".join(slist)))
        for clause in clauseList:
            cwriter.doClause(clause)
        cwriter.finish()

    def generate(self, fname, contextLiterals, ignoreLiterals):
        self.setContext(contextLiterals, ignoreLiterals)
        clauseList = self.reduce()
        self.store(fname, clauseList)
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
    projectionLiterals = None
    sequenceNumber = 0
    cmgr = None
    verbLevel = 1
    rootName = None

    def __init__(self, cnfName, verbLevel = 1):
        creader = readwrite.CnfReader(cnfName, verbLevel)
        cfields = cnfName.split(".")[:-1]
        self.rootName = ".".join(cfields)
        pvars = creader.projectionVariables()
        self.projectionLiterals = set([])
        for v in pvars:
            self.projectionLiterals.add(v)
            self.projectionLiterals.add(-v)
        if verbLevel >= 2 and len(pvars) > 0:
            ilist = sorted([v for v in pvars])
            slist = [str(v) for v in ilist]
            print("GEN: Projection variables: {%s}" % ", ".join(slist))
        self.sequenceNumber = 0
        self.verbLevel = verbLevel
        self.cmgr = ClauseManager(creader.nvar, creader.clauses, verbLevel)
        nnfName = readwrite.changeExtension(cnfName, "nnf")
        self.pog = cnf2pog(cnfName, nnfName, verbLevel)

    def write(self, fname):
        self.pog.write(fname)

    def nextCnfName(self):
        self.sequenceNumber += 1
        return "%s-xxxx-1%.6d.cnf" % (self.rootName, self.sequenceNumber)

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
                if clit not in self.projectionLiterals:
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
        splitLiteral = node.findSplittingLiteral()
        if splitLiteral is None:
            raise ProjectionException("Can't find splitting literal for node %s" % str(ref))
        if splitLiteral in self.projectionLiterals:
            if self.verbLevel >= 3:
                print("  Splitting literal = %d" % splitLiteral)
            cnfName = self.nextCnfName()
            ignoreLiterals = set([splitLiteral, -splitLiteral])
            self.cmgr.generate(cnfName, contextLiterals, ignoreLiterals)
            if isSat(cnfName):
                print("  WARNING: Traversing %s.  CNF file %s satisfiable" % (str(ref), cnfName))
            elif self.verbLevel >= 3:
                print("  Traversing %s.  CNF file %s unsatisfiable" % (str(ref), cnfName))
        nchildren = [self.pog.getRef(lit) for lit in nlits]
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
        elif lit in self.projectionLiterals:
            nlit = readwrite.TautologyId
        else:
            nlit = lit
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
        
