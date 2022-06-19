#!/usr/bin/python3

import sys
import getopt
import writer
import schema


def usage(name):
    print("Usage: %s [-h] [-v] [-p] -n N [-r ROOT]")
    print(" -h      Print this message")
    print(" -v      Add comments to files")
    print(" -p      Generate CRAT proof")
    print(" -n N    Set number of literals")
    print(" -r ROOT Set file root name (default = clause-proto-NNN)")

# Generate CNF and CRAT consisting of single clause with N literals
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
    sch = schema.Schema(n, clauseList, froot, verbLevel = 3 if verbose else 1)
    cwriter = sch.cwriter
    zero = sch.leaf0
    one = sch.leaf1
    literals.reverse()
    # Represent clause as stack of ITEs.  Should get converted to conjunctions
    root = zero
    for lit in literals:
        var = sch.getVariable(abs(lit))
        if lit > 0:
            root = sch.addIte(var, one, root)
        else:
            root = sch.addIte(var, root, one)
    sch.addComment("Assert unit clause for root")
    sch.addClause([root])
    sch.addComment("Delete input clause")
    sch.deleteClause(1)
    cwriter.finish()

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
        root = "clause-proto-" + sn
    cnfGen(root, n, verbose)
    if proof:
        proofGen(root, n, verbose)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
