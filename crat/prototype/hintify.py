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
import os
import getopt
import subprocess
import readwrite


def usage(name):
    print("Usage: %s [-h] [-v VLEVEL] -i FILE.cnf -p IFILE.crat -o OFILE.crat")
    print(" -h           Print this message")
    print(" -v VLEVEL    Set verbosity level (0-3)")
    print(" -i FILE.cnf  Input CNF")
    print(" -p IFILE.crat Input CRAT")
    print(" -o OFILE.crat Output CRAT")

# Where is the binary?
path = os.path.dirname(os.path.realpath(__file__)) + "/crat-lrat"
prog = path + "/" + "crat-lrat"

hintStart = 0
hintList = []
tmpList = []
genLrat = True
deleteTempFiles = False

# Make up a name for intermediate files
def getRoot(cnfName):
    prefix = "tmp_"
    fields = cnfName.split(".")
    if len(fields) > 0:
        fields = fields[:-1]
    fields[0] = prefix + fields[0]
    return ".".join(fields)

def splitFiles(cnfName, cratName, verbLevel):
    try:
        cnfReader = readwrite.CnfReader(cnfName, verbLevel)
    except readwrite.ReadWriteException as ex:
        print("ERROR: Couldn't read input CNF file: %s" % str(ex))
        return
    root = getRoot(cnfName)
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
                    dratWriter.doDelete(lits)
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

def fixLine(line):
    line = line.decode('utf-8')
    while len(line) > 0 and line[0] in ' \n\r':
        line = line[1:]
    while len(line) > 0 and line[-1] in ' \n\r':
        line = line[:-1]
    return line
   

def genHints(root):
    global hintStart, hintList, tmpList
    acnfName = root + ".acnf"    
    dratName = root + ".drat"
    args = [prog, acnfName, dratName, "-f"]
    proc = subprocess.Popen(args, stdout=subprocess.PIPE)
    tmpList += [acnfName, dratName]
    
    lineNumber = 0

    lfile = None
    if genLrat:
        lratName = root + ".lrat"
        try:
            lfile = open(lratName, 'w')
        except:
            print("Couldn't open LRAT file '%s'" % lratName)
            sys.exit(1)

    for line in proc.stdout:
        lineNumber += 1
        line = fixLine(line)
        if len(line) == 0 or line[0] == 'c':
            continue
        if line[-1] != '0':
            continue
        id = 0
        hints = None
        if genLrat:
            lfile.write(line + '\n')
        try:
            fields = line.split()
            ifields = [int(f) for f in fields]
            id = ifields[0]
            pos = ifields.index(0)
            hints = fields[pos+1:]
            hints = hints[:-1]
        except:
            print("Couldn't extract hints from LRAT line #%d: %s" % (lineNumber, str(line)))
            sys.exit(1)
        if id > 0 and hints is not None:
            if hintStart == 0:
                hintStart = id
            if id != hintStart + len(hintList):
                print("LRAT Line #%d has clause Id %d.  Was expecting %d" % (lineNumber, id, hintStart + len(hintList)))
                sys.exit(1)
            hstring = " ".join(hints)
            hintList.append(hstring)
        else:
            print("LRAT.  Couldn't get hints from line #%d: %s" % (lineNumber, str(line)))
            sys.exit(1)
    if genLrat:
        lfile.close()

def getHint(cid):
    if cid < hintStart or cid >= hintStart + len(hintList):
        return None
    return hintList[cid - hintStart]

def insertHints(icratName, hcratName):
    hcount = 0
    try:
        ifile = open(icratName, 'r')
    except:
        print("Couldn't open input CRAT file '%s'" % icratName)
        sys.exit(1)
    try:
        ofile = open(hcratName, 'w')
    except:
        print("Couldn't open output CRAT file '%s'" % hcratName)
        sys.exit(1)
    lineNumber = 0
    for line in ifile:
        lineNumber += 1
        line = readwrite.trim(line)
        if len(line) == 0 or line[0] == 'c':
            ofile.write(line + '\n')
            continue
        fields = line.split()
        cmd = None
        if fields[1] == 'a':
            cmd = fields[1]
            id = int(fields[0])
        elif fields[0] == 'dc':
            cmd = fields[0]
            id = int(fields[1])
        if cmd is None:
            ofile.write(line + '\n')
            continue
        lhint = fields[-2]
        if lhint == '*':
            hstring = getHint(id)
            if hstring is not None:
                fields[-2] = hstring
                nline = " ".join(fields)
                line = nline
                hcount += 1
        ofile.write(line + '\n')
    ifile.close()
    ofile.close()
    print("Added %d hints" % hcount)

def run(name, args):
    cnfName = None
    cratName = None
    hcratName = None
    verbLevel = 1
    optList, args = getopt.getopt(args, "hv:i:p:o:v:")
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
        elif opt == '-o':
            hcratName = val
        else:
            usage(name)
            return
    if cnfName is None or cratName is None or hcratName is None:
        print("Require names for CNF file input CRAT file, and output CRAT file")
        usage(name)
        return

    root = getRoot(cnfName)
    splitFiles(cnfName, cratName, verbLevel)
    genHints(root)
    insertHints(cratName, hcratName)
    if deleteTempFiles:
        for tname in tmpList:
            try:
                os.remove(tname)
            except:
                continue
              

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
                            
            
            
                
            
            

        
        
            
        
    

    
    


