#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
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

# Convert split CRAT proof into files necessary to have hints generated externally

import sys
import getopt
import readwrite

def usage(name):
    print("Usage: %s [-h] [-v VLEVEL] -i FILE.cnf -p FILE.crat -r ROOT")
    print(" -h           Print this message")
    print(" -v VLEVEL    Set verbosity level (0-3)")
    print(" -i FILE.cnf  Input CNF")
    print(" -p FILE.crat Input CRAT")
    print(" -r ROOT      Root for output files.  Will generate ROOT.acnf and ROOT.drat")

def process(cnfName, cratName, root, verbLevel):
    try:
        cnfReader = readwrite.CnfReader(cnfName, verbLevel)
    except readwrite.ReadWriteException as ex:
        print("ERROR: Couldn't read input CNF file: %s" % str(ex))
        return
    acnfName = root + ".acnf"
    cnfWriter = readwrite.AugmentedCnfWriter(cnfReader.nvar, acnfName, verbLevel)
    if verbLevel >= 2:
        cnfWriter.doComment("Original CNF clauses")
    for clause in cnfReader.clauses:
        cnfWriter.doClause(clause)

    # Now get things out of CRAT file
    try:
        cratFile = open(cratName, 'r')
    except:
        print("ERROR: Couldn't open CRAT file '%s'" % cratName)
        return

    try:
        dratName = root + ".drat"
        dratWriter = readwrite.DratWriter(dratName)
    except:
        print("ERROR: Couldn't open output DRAT file '%s'" % dratName)
        return

    lineNumber = 0
    dratClauses = 0    
    getProducts = True
    for line in cratFile:
        line = readwrite.trim(line)
        lineNumber += 1
        fields = line.split()
        if len(fields) == 0 or fields[0][0] == 'c':
            continue
        try:
            id = int(fields[0])
        except:
            # Hit command that requires no action
            break
        try:
            cmd = fields[1]
            rest = fields[2:]
        except:
            print("ERROR: File %s, line #%d.  Couldn't parse line '%s' in CRAT file" % (cratName, lineNumber, line))
            return
        if cmd == 'p' and getProducts:
            try:
                ilist = [int(r) for r in rest[:-1]]
                var = ilist[0]
                args = ilist[1:]
                cnfWriter.doProduct(var, args)
            except:
                print("ERROR: File %s, line #%d.  Couldn't parse product line '%s' in CRAT file" % (cratName, lineNumber, line))                
                return
        elif cmd == 'a':
            getProducts = False
            if rest[-2] == '*':
                try:
                    lits = [int(r) for r in rest[:-3]]
                    dratWriter.doStep(lits)
                    dratClauses += 1
                except:
                    print("ERROR:  File %s, line #%d. Couldn't generate DRAT step from line %s" % (cratName, lineNumber, line))
                    return
            else:
                break
        else:
            break
    cratFile.close()
    print("Input CNF file %s had %d variables and %d clauses" % (cnfName, cnfReader.nvar, len(cnfReader.clauses)))
    cnfWriter.finish()
    vcount = cnfWriter.variableCount()
    vmax = cnfWriter.expectedVariableCount
    print("Augmented CNF file %s has %d variables (max=%d) and %d clauses" % (acnfName, vcount, vmax, cnfWriter.clauseCount))
    dratWriter.finish()
    print("DRAT file %s has %d clauses" % (dratName, dratClauses))

def run(name, args):
    cnfName = None
    cratName = None
    root = None
    verbLevel = 1
    optList, args = getopt.getopt(args, "hv:i:p:r:v:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            cratName = val
        elif opt == '-r':
            root = val
        else:
            usage(name)
            return
    if cnfName is None or cratName is None or root is None:
        print("Require names for CNF file and CRAT file, plus root name for output files")
        usage(name)
        return

    process(cnfName, cratName, root, verbLevel)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
                            
            
            
                
            
            

        
        
            
        
    

    
    


