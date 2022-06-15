#!/usr/bin/python

import getopt
import sys

import writer

# Generate CNF representation of n-queens problem

def usage(name):
    print("Usage: %s [-h] [-v] [-V (o|b)] [-C (s|d)] [-n N] [-r froot]" % name)
    print(" -h       Print this message")
    print(" -v       Verbose")
    print(" -V VENC  Encode variables in binary (b) or one-hot")
    print(" -C EENC  Encode constraints with direct (d) or Sinz (s) method")
    print(" -n N     Specify board size")
    print(" -r froot Specify root of file names")


def unitRange(n):
    return range(1,n+1)


# Set of objects mapped to row/column entries in a 2-d grid
# Rows and columns numbered starting at 1
class RCMap:

    mapDict = {}
    nrow = 0
    ncol = 0

    def __init__(self, nrow, ncol):
        self.nrow = nrow
        self.ncol = ncol
        self.mapDict = {}
        for r in unitRange(nrow):
            for c in unitRange(ncol):
                self.mapDict[(r,c)] = []

    def addEntry(self, row, col, val):
        self.mapDict[(row,col)].append(val)

    def getEntries(self, row, col):
        return self.mapDict[(row,col)]

    def allValues(self):
        result = []
        for r in unitRange(self.nrow):
            for c in unitRange(self.ncol):
                result = result + self.mapDict[(r,c)]
        return result

class Queen:
    N = 8
    froot = None
    pwriter = None
    verbose = False

    
    # Set of input variables, mapped to specific squares
    inputMap = None
    # set of variables encoding whether or not each square r,c is
    # occupied.  Indexed as (r,c)
    squareVarDict = {}
    # Set of Tseitin variables associated with each square r,c
    tseitinMap = None
    # List of clauses and comments.
    # Each list element is a pair (isComment, entry),
    # where entry is either string or list of literals
    commentsAndClauses = []

    varCount = 0

    ## Encoding methods
    # How at-most-one constraints encoded
    direct = True
    # How occupancy of each row encoded
    binary = True


    def __init__(self, froot, N, direct = True, binary = False, verbose = False):
        self.N = N
        self.froot = froot
        self.direct = direct
        self.binary = binary
        self.verbose = verbose
        self.inputMap = RCMap(self.N, self.N)
        self.squareVars = {}
        self.tseitinMap = RCMap(self.N, self.N)
        self.commentsAndClauses = []
        self.varCount = 0
        vtype = "binary" if self.binary else "one-hot"
        etype = "direct" if self.direct else "Sinz"
        self.addComment("Generation of %d-queens problem with %s variables and %s constraints" % (self.N, vtype, etype))
        if self.binary:
            self.setupBinary()
        else:
            self.setupOneHot()

    def addComment(self, com):
        self.commentsAndClauses.append((True, com))

    def addClause(self, cls):
        self.commentsAndClauses.append((False, cls))

    def allocateInput(self, row, col):
        self.varCount += 1
        v = self.varCount
        self.inputMap.addEntry(row, col, v)
        return v
        
    # Allocate Tseitin variable associated with particular row and column
    def allocateTseitin(self, row, col):
        self.varCount += 1
        v = self.varCount
        self.tseitinMap.addEntry(row, col, v)
        return v

    # Generate list of literals encoding binary representation of x-1
    def getBitLiterals(self, x, vars):
        # Numbers x start at 1
        xm1 = x-1
        k = len(vars)
        bits = [((x>>i)&1) for i in range(k)]
        lits = [-v if b == 0 else v for (v,b) in zip(vars, bits)]
        return lits

    # Set up input variables, using either binary or one-hot encoding
    def setupBinary(self):
        logN = 1
        while (2**logN) < self.N:
            logN += 1
        # Introduce logN variables for each row, encoding position of queen
        # Must allocate all input variables before any Tseitin variables
        rvarMap = {}
        for r in unitRange(self.N):
            rvarMap[r]= [self.allocateInput(r, 1) for i in range(logN)]
        for r in unitRange(self.N):
            rvars = rvarMap[r]
            for c in unitRange(self.N):
                v = self.allocateTseitin(r, c)
                lits = self.getBitLiterals(c, rvars)
                self.addComment("Encoding of square variable %d r=%d, c=%d" % (v, r, c))
                self.addClause(lits + [v])
                for lit in lits:
                    self.addClause([-lit, -v])
                self.squareVars[(r,c)] = v
                
    def setupOneHot(self):
        for r in unitRange(self.N):
            for c in unitRange(self.N):
                v = self.allocateInput(r, c)
                self.squareVars[(r,c)] = v

    def inputVarRange(self, rstart, cstart, rend, cend):
        count = max(abs(rend-rstart), abs(cend-cstart)) + 1
        dr = 1 if rend-rstart > 0 else -1 if rend-rstart < 0 else 0
        dc = 1 if cend-cstart > 0 else -1 if cend-cstart < 0 else 0
        vlist = []
        r = rstart
        c = cstart
        rstop = rend+dr
        cstop = cend+dc
        vlist = []
        while (r != rstop or c != cstop):
            v = self.squareVars[(r, c)]
            vlist.append(v)
            r += dr
            c += dc
        return vlist

    # Create enough Sinz variables to encode AMO constraint between two points
    # Length will be 2 less than range of r, c vars.
    def sinzVarRange(self, rstart, cstart, rend, cend):
        count = max(abs(rend-rstart), abs(cend-cstart)) - 1
        if count < 1:
            return []
        dr = 1 if rend-rstart > 0 else -1 if rend-rstart < 0 else 0
        dc = 1 if cend-cstart > 0 else -1 if cend-cstart < 0 else 0
        vlist = []
        r = rstart + dr
        c = cstart + dc
        rstop = rend
        cstop = cend
        vlist = []
        while (r != rstop or c != cstop):
            v = self.allocateTseitin(r, c)
            vlist.append(v)
            r += dr
            c += dc
        return vlist

    def atMostOneDirect(self, litList):
        nmax = len(litList)
        for i in range(nmax):
            for j in range(i+1,nmax):
                clause = [-litList[i], -litList[j]]
                self.addClause(clause)

    # Sinz encoding of AMO.  Requires
    # len(auxList) = len(litList) - 2
    def atMostOneSinz(self, litList, auxList):
        k = len(litList)
        if k <= 2:
            self.atMostOneDirect(litList)
            return
        # Get things started
        x1 = litList[0]
        x2 = litList[1]
        s2 = auxList[0]
        self.addClause([-x1,  s2]) # Propagate
        self.addClause([-x2,  s2]) # Generate
        self.addClause([-x1, -x2]) # Suppress
        for i in range(3, k):
            xi = litList[i-1]
            si = auxList[i-2]
            sim1 = auxList[i-3]
            self.addClause([-sim1,  si])  # Propagate
            self.addClause([-xi,    si])  # Generate
            self.addClause([-sim1, -xi])  # Suppress
        snm1 = auxList[k-3]
        xn = litList[k-1]
        self.addClause([-snm1, -xn]) # Suppress
            
    def aloRange(self, rstart, cstart, rend, cend):
        ilist = self.inputVarRange(rstart, cstart, rend, cend)
        self.addClause(ilist)

    def amoRange(self, rstart, cstart, rend, cend):
        ilist = self.inputVarRange(rstart, cstart, rend, cend)
        if self.direct:
            self.atMostOneDirect(ilist)
        else:
            alist = self.sinzVarRange(rstart, cstart, rend, cend)
            self.atMostOneSinz(ilist, alist)
            
    def amoRow(self, row):
        self.amoRange(row, 1, row, self.N)

    def aloRow(self, row):
        self.aloRange(row, 1, row, self.N)

    def amoCol(self, col):
        self.amoRange(1, col, self.N, col)

    def amoDiagDR(self, index):
        if index < 0:
            rstart = 1-index
            cstart = 1
            rend = self.N
            cend = self.N+index
        else:
            rstart = 1
            cstart = index+1
            rend = self.N-index
            cend = self.N
        self.amoRange(rstart, cstart, rend, cend)

    def amoDiagDL(self, index):
        if index < 0:
            rstart = 1
            cstart = self.N+index
            rend = self.N+index
            cend = 1
        else:
            rstart = index+1
            cstart = self.N
            rend = self.N
            cend = index+1
        self.amoRange(rstart, cstart, rend, cend)

    def generateQCNF(self):
        cwriter = writer.QcnfWriter(self.froot, self.verbose)
        # Build clauses
        if self.binary:
            for r in unitRange(self.N):
                if self.verbose:
                    self.addComment("At least one constraint for row %d" % r)
                self.aloRow(r)
        else:
            for r in unitRange(self.N):
                if self.verbose:
                    self.addComment("Exactly one constraints for row %d" % r)
                self.amoRow(r)
                self.aloRow(r)
        for c in unitRange(self.N):
            if self.verbose:
                self.addComment("At most one constraints for column %d" % c)
            self.amoCol(c)
        for d in range(-self.N+2,self.N-1):
            if self.verbose:
                self.addComment("At most one constraints for DR diagonal %d" % d)
            self.amoDiagDR(d)
        for d in range(-self.N+2,self.N-1):
            if self.verbose:
                self.addComment("At most one constraints for DL diagonal %d" % d)
            self.amoDiagDL(d)
        
        # Declare variables
        cwriter.addVariables(0, self.inputMap.allValues(), True)
        for r in unitRange(self.N):
            for c in unitRange(self.N):
                tlist =self.tseitinMap.getEntries(r,c)
                if len(tlist) > 0:
                    idx = (r-1)*self.N + c
                    cwriter.doVariableComment(idx, "Tseitin variables for r=%d, c=%d" % (r,c))
                    cwriter.addVariables(idx, tlist, True)

        # Generate clauses and comments
        for (isComment, entry) in self.commentsAndClauses:
            if isComment:
                cwriter.doComment(entry)
            else:
                cwriter.doClause(entry)
        cwriter.finish()
                                
    def generateOrder(self):
        pwriter = writer.OrderWriter(self.varCount, self.froot, self.verbose)
        for r in unitRange(self.N):
            for c in unitRange(self.N):
                pwriter.doOrder(self.inputMap.getEntries(r, c) + self.tseitinMap.getEntries(r, c))
        pwriter.finish()

def run(name, args):
    N  = 8
    verbose = False
    doBinary = False
    doDirect = True
    froot = None
    optlist, args = getopt.getopt(args, "hvV:C:n:r:")
    # [-h] [-v] [-V (o|b)] [-C (s|d)] [-n N] [-r froot]" % name)
    for opt, val in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-V':
            if val == 'b':
                doBinary = True
            elif val != 'o':
                print("Uknown variable encoding option '%s'" % val)
                usage(name)
                return
        elif opt == '-C':
            if val == 's':
                doDirect = False
            elif val != 'd':
                print("Uknown constraint encoding option '%s'" % val)
                usage(name)
                return
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

    queen = Queen(froot, N, doDirect, doBinary, verbose)
    queen.generateQCNF()
    queen.generateOrder()


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
    
    

    
