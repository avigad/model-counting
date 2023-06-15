#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

# Encode XOR-PAIRS problem described in:
# O. Beyersdorff, T. Hoffman, L. N. Spachmann,
# "Proof Complexity of Propositional Model Counting"
# SAT 2023

import sys
import  getopt
import writer
import cnf_utilities

# Generate CNF file for pigeonhole problem
def usage(name):
    print("Usage: %s [-h] [-v] -r ROOT -n N" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf")
    print("  -n N     Specify size parameter")

def generate(froot, N, verbose):
    cwriter = writer.LazyCnfWriter(froot)
    X = cwriter.newVariables(N)
    Y = cwriter.newVariables(N)
    Z = cwriter.newVariables(N*N)
    if verbose:
        cwriter.doComment("Encoding of XOR-PAIRS problem for N=%d" % N)
        cwriter.doComment("X: %d--%d, Y: %d--%d, Z:%d--%d" % (X[0], X[N-1], Y[0], Y[N-1], Z[0], Z[N*N-1]))
    for i in range(N):
        x = X[i]
        for j in range(N):
            y = Y[j]
            z = Z[N*i + j]
            if verbose:
                cwriter.doComment("Parity constraint for X[%d], Y[%d], Z[%d,%d]" % (i+1, j+1, i+1, j+1))
            cnf_utilities.parityDirect(cwriter, [x, y, z], 0)
    cwriter.finish()
    
def run(name, args):
    verbose = False
    N = None
    froot = None
    optlist, args = getopt.getopt(args, "hvr:n:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-r':
            froot = val
        elif opt == '-n':
            N = int(val)
    if N is None:
        print("Must have value for N")
        usage(name)
    if froot is None:
        print("Must have root name")
        usage(name)
        return
    generate(froot, N, verbose)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
