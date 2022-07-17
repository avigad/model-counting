#!/usr/bin/python3

import sys
import getopt
import readwrite
import schema


def usage(name):
    print("Usage: %s [-h] [-v] -n N [-o FILE.cnf] [-p FILE.crat]")
    print(" -h           Print this message")
    print(" -v           Add comments to files")
    print(" -n N         Set number of literals")
    print(" -o FILE.cnf  CNF file name (default = clause-proto-NNN.cnf)")
    print(" -p FILE.crat CRAT file name (default = clause-proto-NNN.cnf)")

# Generate CNF and CRAT consisting of single clause with N literals
literals = []
clauseList = []

def cnfGen(fname, n, verbose):
    global literals, clauseList
    cwriter = readwrite.LazyCnfWriter(fname)
    if verbose:
        cwriter.doComment("CNF file consisting of single clause with %d literals" % n)
    vars = cwriter.newVariables(n)
    literals = [v if v%2==0 else -v for v in vars]
    cwriter.doClause(literals)
    clauseList = cwriter.clauseList()
    cwriter.finish()

def proofGen(fname, n, verbose):
    sch = schema.Schema(n, clauseList, fname, verbLevel = 3 if verbose else 1)
    cwriter = sch.cwriter
    children = []
    for lit in literals:
        child = sch.getVariable(abs(lit))
        if lit > 0:
            child = sch.addNegation(child)
        children.append(child)
    sch.addComment("Form conjunction of negated literals")
    negroot = sch.addConjunction(children)
    root = sch.addNegation(negroot)
    sch.addComment("Assert unit clause for negated root")
    sch.addClause([root])
    sch.addComment("Delete input clause")
    sch.deleteClause(1)
    cwriter.finish()

def run(name, args):
    verbose = False
    cnfName = None
    cratName =None
    sn = None
    root = None
    optlist, args = getopt.getopt(args, 'hvp:n:o:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-p':
            cratName = None
        elif opt == '-n':
            sn = val
        elif opt == '-o':
            cnfName = val
    if sn is None:
        print("Must provide value of n")
        usage(name)
        return
    n = int(sn)
    if cnfName is None:
        cnfName = "clause-proto-" + sn + ".cnf"
    if cratName is None:
        cratName = "clause-proto-" + sn + ".crat"
    cnfGen(cnfName, n, verbose)
    proofGen(cratName, n, verbose)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
