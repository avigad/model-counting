#!/usr/bin/python

import getopt
import sys

import writer

# Generate CNF representation of n-queens problem

def usage(name):
    print("Usage: %s [-h] [-v] [-p] [-s] [-n N] [-r froot]" % name)
    print(" -h       Print this message")
    print(" -v       Verbose")
    print(" -s       Use Sinz encoding")
    print(" -p       Generate permutation file for BDD variable ordering")
    print(" -n N     Specify board size")
    print(" -r froot Specify root of file names")


def unitRange(n):
    return range(1,n+1)


class Queen:
    N = 8
    cwriter = None
    verbose = False

    def __init__(self, cwriter, N, verbose = False):
        self.cwriter = cwriter
        self.N = N
        self.direct = True
        self.verbose = verbose

    def atMostOneDirect(self, litList):
        nmax = len(litList)
        for i in range(nmax):
            for j in range(i+1,nmax):
                clause = [-litList[i], -litList[j]]
                self.cwriter.doClause(clause)

    def atLeastOne(self, litList):
        self.cwriter.doClause(litList)

    # Return variable for square row, col (1 ... N)
    def squareVar(self, row, col):
        return col + (row-1)*self.N

    def rowList(self, row):
        return [self.squareVar(row, c) for c in unitRange(self.N)]

    def colList(self, col):
        return [self.squareVar(r, col) for r in unitRange(self.N)]

    # Downward-right diagonal.  Index from -(N-1) to +(N-1)
    def diagDR(self, index):
        if index < 0:
            rstart = 1-index
            cstart = 1
            count = self.N+index
        else:
            rstart = 1
            cstart = index+1
            count = self.N-index
        return [self.squareVar(i+rstart, i+cstart) for i in range(count)]

    # Downward-left diagonal.  Index from -(N-1) to +(N-1)
    def diagDL(self, index):
        if index < 0:
            rstart = 1
            cstart = self.N+index
            count = self.N+index
        else:
            rstart = index+1
            cstart = self.N
            count = self.N-index
        return [self.squareVar(i+rstart, -i+cstart) for i in range(count)]
    
    def generateDirect(self):
        self.cwriter.doComment("Generation of %d-queens problem using direct encoding" % self.N)
        vars = list(unitRange(self.N*self.N))
        self.cwriter.addVariables(0, vars, True)
        for r in unitRange(self.N):
            if self.verbose:
                self.cwriter.doComment("Exactly one constraints for row %d" % r)
            rlist = self.rowList(r)
            self.atMostOneDirect(rlist)
            self.atLeastOne(rlist)
        for c in unitRange(self.N):
            if self.verbose:
                self.cwriter.doComment("At most one constraints for column %d" % c)
            clist = self.colList(c)
            self.atMostOneDirect(clist)
        for d in range(-self.N+2,self.N-1):
            if self.verbose:
                self.cwriter.doComment("At most one constraints for DR diagonal %d" % d)
            drlist = self.diagDR(d)
            self.atMostOneDirect(drlist)
        for d in range(-self.N+2,self.N-1):
            if self.verbose:
                self.cwriter.doComment("At most one constraints for DL diagonal %d" % d)
            dllist = self.diagDL(d)
            self.atMostOneDirect(dllist)

def run(name, args):
    N  = 8
    verbose = False
    doSinz = False
    doPerm = False
    froot = None
    optlist, args = getopt.getopt(args, "hvspn:r:")
    for opt, val in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-p':
            doPerm = True
        elif opt == '-v':
            verbose = True
        elif opt == '-s':
            doSinz = True
        elif opt == '-n':
            N = int(val)
        elif opt == '-r':
            froot = val
        else:
            print("Invalid option '%s'" % opt)
            usage(name)
            return

    if froot is None:
        print("Must specify output file root")
        usage(name)
        return

    cwriter = writer.QcnfWriter(froot)
    queen = Queen(cwriter, N, verbose)
    queen.generateDirect()
    cwriter.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
    
    

    
