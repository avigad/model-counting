#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
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

import sys
import  getopt
import random

import writer
import cnf_utilities


# Generate CNF file for at-most-one constraints
def usage(name):
    print("Usage: %s [-h] [-v] [-m d|s|t] [-f FIRST] -r ROOT -n N" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -m NODE  Specify encoding method: direct (d), Sinz (s), or Tseitin (t)")
    print("  -f FIRST Specify value of first variable (default = 1)")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf")
    print("  -n N     Specify number of elements")


directMode, sinzMode, tseitinMode = list(range(3))
modeDict = {'d' : directMode, 's' : sinzMode, 't' : tseitinMode}
modeNames = {directMode : 'Direct', sinzMode : 'Sinz', tseitinMode : 'Tseitin' }

verbose = False
elementCount = 8
mode = directMode
firstVariable = 1

# For weighted model counting.
# Index from 1

def wi(i):
    random.seed(i)
    return random.randint(1,999) * 0.001

def generate(froot):
    cwriter = writer.LazyCnfWriter(froot, verbLevel = 2 if verbose else 1)
    if verbose:
        cwriter.doHeaderComment("Encoding of at-most-one constraint for %d elements" % (elementCount))
        cwriter.doHeaderComment("Use %s encoding of at-most-one constraints" % modeNames[mode])
    cwriter.doHeaderComment("t wmc" if mode == directMode else "t pwmc")
    if (firstVariable > 1):
        cwriter.newVariables(firstVariable-1)
    vars = cwriter.newVariables(elementCount)
    if mode == sinzMode:
        cnf_utilities.atMostOneSinz(cwriter, vars, verbose)
    elif mode == tseitinMode:
        cnf_utilities.atMostOneTseitin(cwriter, vars, verbose)
    else:
        cnf_utilities.atMostOneDirect(cwriter, vars, verbose)
    if mode != directMode:
        slist = [str(i) for i in vars]
        cwriter.doComment("p show %s 0" % " ".join(slist))
    for i in vars:
        cwriter.doComment("p weight %d %.3f 0" % (i, wi(i)))
    cwriter.finish()

def run(name, args):
    global verbose, elementCount, mode, firstVariable
    froot = None
    elementCount = None
    optlist, args = getopt.getopt(args, "hvf:r:n:m:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-r':
            froot = val
        elif opt == '-f':
            firstVariable = int(val)
        elif opt == '-n':
            elementCount = int(val)
        elif opt == '-m':
            if val in modeDict:
                mode = modeDict[val]
            else:
                print("Unknown encoding mode '%s'" % val)
                usage(name)
                return
    if elementCount is None:
        print("Must have value for n")
        usage(name)
        return
    if froot is None:
        print("Must have root name")
        usage(name)
        return
    generate(froot)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        
