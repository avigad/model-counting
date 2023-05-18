#!/usr/bin/python3

# Remove tautologies from CNF file
import sys
import readwrite

def usage(name):
    print("Usage: %s INFILE.cnf OUTFILE.cnf")

def process(iname, oname):
    icount = 0
    ncount = 0
    creader = readwrite.CnfReader(iname, check = False)
    try:
        pass
    except Exception as ex:
        print("Failed to read CNF file %s: %s" % (iname, str(ex)))
        return
    try:
        cwriter = readwrite.CnfWriter(creader.nvar, oname)
    except Exception as ex:
        print("Failed to open CNF output file %s: %s" % (oname, str(ex)))
        return
    for clause in creader.clauses:
        icount += 1
        nclause = readwrite.cleanClause(clause)
        if nclause != readwrite.tautologyId:
            ncount += 1
            cwriter.doClause(clause)
    cwriter.finish()
    print("Processed %d clauses in file %s.  Wrote %d clauses to file %s" % (icount, iname, ncount, oname))

def run(name, args):
    if len(args) != 2:
        usage(name)
        return
    process(args[0], args[1])

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

