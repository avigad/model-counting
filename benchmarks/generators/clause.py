#!/usr/bin/python3

import sys
import getopt
import writer

def usage(name):
    print("Usage: %s [-h] [-v] [-p] -n N [-r ROOT]")
    print(" -h      Print this message")
    print(" -v      Add comments to files")
    print(" -p      Generate CRAT proof")
    print(" -n N    Set number of literals")
    print(" -r ROOT Set file root name (default = clause-NNN)")

# Generate CNF consisting of single clause with N literals
literals = []
clauseList = []

def cnfGen(froot, n, verbose):
    global literals, clauseList
    cwriter = writer.LazyCnfWriter(froot)
    if verbose:
        cwriter.doComment("CNF file consisting of single clause with %d literals" % n)
    vars = cwriter.newVariables(n)
    literals = [v if v%2==0 else -v for v in vars]
    cwriter.doClause(literals)
    clauseList = cwriter.clauseList()
    cwriter.finish()

def proofGen(froot, n, verbose):
    pwriter = writer.CratWriter(n, clauseList, froot, verbose)
    # Create chain of AND operations, using negated inputs
    pwriter.doComment("Create chain of %d AND operations with negated inputs" % (n-1))
    args = [-lit for lit in literals]
    upSteps = []
    downSteps = []
    while len(args) > 1:
        step = pwriter.stepCount + 1
        arg1 = args[-2]
        arg2 = args[-1]
        downSteps += [step]
        upSteps += [step+1, step+2]
        (v, s) = pwriter.doAnd(arg1, arg2)
        args = args[:-2] + [v]
    # Assert unit clause for root
    root = -args[0]
    pwriter.doComment("Assert unit clause for root")
    upSteps.reverse()
    pwriter.doClause([root], upSteps + [1])
    step = pwriter.stepCount
    # Delete input clause
    pwriter.doComment("Delete input clause")
    pwriter.doDeleteClause(1, downSteps + [step])
    pwriter.finish()

def run(name, args):
    verbose = False
    proof = False
    sn = None
    root = None
    optlist, args = getopt.getopt(args, 'hvpn:r:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-p':
            proof = True
        elif opt == '-n':
            sn = val
        elif opt == '-r':
            root = val
    if sn is None:
        print("Must provide value of n")
        usage(name)
        return
    n = int(sn)
    if root is None:
        root = "clause-" + sn
    cnfGen(root, n, verbose)
    if proof:
        proofGen(root, n, verbose)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
