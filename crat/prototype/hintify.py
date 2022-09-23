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
import datetime
import readwrite


def usage(name):
    print("Usage: %s [-h] [-s SMODE] [-v VLEVEL] -i FILE.cnf -p IFILE.crat -o OFILE.crat")
    print(" -h           Print this message")
    print(" -s SMODE     Set mode for splitting proof: 1=all steps included (default) 2=requires SAT solver")
    print(" -v VLEVEL    Set verbosity level (0-3)")
    print(" -i FILE.cnf  Input CNF")
    print(" -p IFILE.crat Input CRAT")
    print(" -o OFILE.crat Output CRAT")

# Where is the binary?
dpath = os.path.dirname(os.path.realpath(__file__)) + "/crat-lrat"
drat_trim_prog = dpath + "/" + "crat-lrat"

interpreter = "python3"
jpath = os.path.dirname(os.path.realpath(__file__))
justify_prog = jpath + "/" + "justify.py"

# Clauses requiring hint addition
# First clause Id
hintStart = 0
# Mapping from original Id to new Id for hint addition/deletion
hintIdMap = {}
# List of hints
hintList = []
# For split mode 2, list of asserted clauses
clauseList = []

# Temporary file names.  Optionally deleted
tmpList = []

# Debugging options
genLrat = False
deleteTempFiles = True

# Make up a name for intermediate files
def getRoot(cnfName):
    prefix = "tmp_"
    fields = cnfName.split(".")
    if len(fields) > 0:
        fields = fields[:-1]
    fields[0] = prefix + fields[0]
    return ".".join(fields)

def splitFiles(cnfName, cratName, verbLevel):
    global tmpList
    try:
        cnfReader = readwrite.CnfReader(cnfName, verbLevel)
    except readwrite.ReadWriteException as ex:
        print("ERROR: Couldn't read input CNF file: %s" % str(ex))
        return
    cnfWriter = readwrite.AugmentedCnfWriter(cnfReader.nvar, acnfName, verbLevel)
    tmpList.append(acnfName)
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
        dratWriter = readwrite.DratWriter(dratName)
    except Exception as ex:
        print("ERROR: Couldn't open output DRAT file '%s' (%s)" % (dratName, str(ex)))
        return
    tmpList.append(dratName)

    lineNumber = 0
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
                cnfWriter.doProduct(var, args, dwriter = dratWriter)
            except:
                print("ERROR: File %s, line #%d.  Couldn't parse product line '%s' in CRAT file" % (cratName, lineNumber, line))                
                return
        elif cmd == 'a':
            getProducts = False
            if rest[-2] == '*':
                try:
                    lits = [int(r) for r in rest[:-3]]
                    dratWriter.doStep(lits)
                except:
                    print("ERROR:  File %s, line #%d. Couldn't generate DRAT step from line %s" % (cratName, lineNumber, line))
                    return
            else:
                break
        else:
            break
    cratFile.close()
    print("HINTIFY: Input CNF file %s had %d variables and %d clauses" % (cnfName, cnfReader.nvar, len(cnfReader.clauses)))
    cnfWriter.finish()
    vcount = cnfWriter.variableCount()
    vmax = cnfWriter.expectedVariableCount
    print("HINTIFY: Augmented CNF file %s has %d variables (max=%d) and %d clauses" % (acnfName, vcount, vmax, cnfWriter.clauseCount))
    dratWriter.finish()
    print("HINTIFY: DRAT file %s has %d clause additions and %d clause deletions" % (dratName, dratWriter.additions, dratWriter.deletions))

def fixLine(line):
    line = line.decode('utf-8')
    while len(line) > 0 and line[0] in ' \n\r':
        line = line[1:]
    while len(line) > 0 and line[-1] in ' \n\r':
        line = line[:-1]
    return line
   

def genHints(verbLevel):
    global hintStart, hintIdMap, hintList
    args = [drat_trim_prog, acnfName, dratName, "-f"]
    proc = subprocess.Popen(args, stdout=subprocess.PIPE)
    
    lineNumber = 0

    lfile = None
    if genLrat:
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
            hintIdMap[id] = id
        else:
            print("LRAT.  Couldn't get hints from line #%d: %s" % (lineNumber, str(line)))
            sys.exit(1)
    if genLrat:
        lfile.close()

def newClauseId(cid):
    if cid < hintStart or cid >= hintStart + len(hintIdMap):
        return cid
    return hintIdMap[cid]

def getHint(cid):
    if cid < hintStart or cid >= hintStart + len(hintIdMap):
        return None
    ncid = newClauseId(cid)
    return hintList[ncid - hintStart]

def insertHintsMode1(icratName, hcratName, verbLevel):
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
    print("HINTIFY: Added %d hints" % hcount)

def justifyAssertions(verbLevel):
    global tmpList
    args = [interpreter, justify_prog, '-v', str(verbLevel), '-i', acnfName, '-d', dratName, '-o', lratName]
    if verbLevel >= 2:
        print("HINTIFY: Running '%s'" % " ".join(args))
    tmpList.append(lratName)
    proc = subprocess.Popen(args)
    proc.wait()
    if proc.returncode != 0:
        astring = " ".join(args)
        print("ERROR: Running '%s' gave return code of %d" % (astring, proc.returncode))
        sys.exit(1)

def insertHintsMode1(icratName, hcratName, verbLevel):
    ahcount = 0
    dhcount = 0
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
        if fields[1] == 'a':
            cmd = fields[1]
            id = int(fields[0])
        elif fields[0] == 'dc':
            cmd = fields[0]
            id = int(fields[1])
        else:
            ofile.write(line + '\n')
            continue
        lhint = fields[-2]
        if lhint == '*':
            hstring = getHint(id)
            if hstring is not None:
                fields[-2] = hstring
                nline = " ".join(fields)
                line = nline
                if cmd == 'a':
                    ahcount += 1
                else:
                    dhcount += 1
        ofile.write(line + '\n')
    ifile.close()
    ofile.close()
    if verbLevel >= 1:
        print("HINTIFY: Added hints to %d assertions and %d deletions.  Total = %d" % (ahcount, dhcount, ahcount+dhcount))


# For mode 2, need to construct mapping from asserted clauses to
# position in sequence
# Also store the clauses and the hints to enable deletion
def buildHints(verbLevel):
    global hintIdMap, hintList, clauseList
    dreader = readwrite.DratReader(dratName)
    lreader = readwrite.LratReader(lratName)
    initialId = hintStart

    isteps = 0
    lsteps = 0
    while True:
        key, dclause = dreader.readStep()
        if key is None:
            break
        elif key == 'd':
            continue
        if verbLevel >= 3:
            print("HINTIFY: Expanding Assertion #%d: %s" % (initialId, str(dclause)))
        isteps += 1
        while True:
            key, id, lclause, hints = lreader.readStep()
            if key is None:
                print("Ran out of clauses in LRAT file while justifying assertion #%d %s" % (initialId, str(dclause)))
                sys.exit(1)
            elif key == 'a':
                lsteps += 1
                clauseList.append(lclause)
                hintList.append(hints)
                if verbLevel >= 3:
                    print("HINTIFY:      Clause %s, Hints %s" % (str(lclause), str(hints)))
                if readwrite.testClauseEquality(dclause, lclause):
                    hintIdMap[initialId] = id
                    if verbLevel >= 3:
                        print("Assertion #%d --> Proof step %d" % (initialId, id))
                    break
        initialId += 1
    if verbLevel >= 2:
        print("HINTIFY: Replaced %d assertions with %d clauses" % (isteps, lsteps))
    dreader.finish()
    lreader.finish()

# Given list of integers encoding clause + hints
# Fix the hints to be to the correct points in the proof
# Return (vals, changed)
def fixHints(vals, hintOnly, verbLevel):
    gotClause = hintOnly
    changed = False
    nvals = []
    for val in vals:
        if val == 0:
            nvals.append(val)
            if not gotClause:
                gotClause = True
        elif gotClause:
            nval = newClauseId(val)
            nvals.append(nval)
            changed = changed or (nval != val)
        else:
            nvals.append(val)
    if verbLevel >= 3 and changed:
        sline = " ".join([str(val) for val in vals])
        nsline = " ".join([str(val) for val in nvals])
        print("Clause + Remapped hints: %s --> %s" % (sline, nsline))
    return (nvals, changed)


# Convert input CRAT file into hinted CRAT file
# for case where assertions in CRAT required justification by 
# SAT solver
def insertHintsMode2(icratName, hcratName, verbLevel):
    # Operation proceeds in several phases:
    # Phase 1: Process lemma argument operations in input CRAT.  Pass to HCRAT
    # Phase 2: Replace unhinted assertions in input CRAT with sequence of hinted clauses from LRAT file
    #          Also build hintIdMap
    # Phase 3: Process remaining operations and hinted assertions in input CRAT.
    #          Must renumber clause Ids in hints
    # Phase 4: Replace sequence of unhinted clause deletions with deletions of all hinted clauses from LRAT file in reverse order
    # Phase 5: Process input clause deletions from input CRAT.  Pass to HCRAT

    global hintStart

    # Flags to signal phase transitions
    replacedAssertions = False
    replacedDeletions = False

    # (Added,deleted) (additions,assertions)
    aacount = 0
    dacount = 0
    adcount = 0
    ddcount = 0
    cacount = 0
    cdcount = 0

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
        if len(fields) < 2:
            ofile.write(line + '\n')
            continue
        if fields[0] == 'dc':
            cmd = fields[0]
            id = int(fields[1])
        elif fields[1] == 'a':
            cmd = fields[1]
            id = int(fields[0])
        else:
            ofile.write(line + '\n')
            continue
        lhint = fields[-2]
        if cmd == 'a' and lhint == '*':
            if replacedAssertions:
                # Assertion is obsolete.
                dacount += 1
                continue
            else:
                hintStart = id
                buildHints(verbLevel)
                # Dump all of the clauses and hints from the  LRAT file
                for clause, hints in zip(clauseList, hintList):
                    sclause = " ".join([str(lit) for lit in clause])
                    shint = " ".join([str(hint) for hint in hints])
                    ofile.write("%d a %s 0 %s 0\n" % (id, sclause, shint))
                    id += 1
                    aacount += 1
                replacedAssertions = True
                dacount += 1
        elif cmd == 'dc' and lhint == '*':
            if replacedDeletions:
                # Deletion is obsolete
                ddcount += 1
                continue
            else:
                cid = hintStart + len(clauseList) - 1
                while cid >= hintStart:
                    hints = hintList[cid-hintStart]
                    shint = " ".join([str(hint) for hint in hints])
                    ofile.write("dc %d %s 0\n" % (cid, shint))
                    cid -= 1
                    adcount += 1
                replacedDeletions = True
                ddcount += 1
        else:
            # Hinted assertion or deletion.  Must remap hints
            hintOnly = cmd == 'dc'
            nfields,changed = fixHints([int(field) for field in fields[2:]], hintOnly, verbLevel)
            if changed:
                if cmd == 'a':
                    cacount += 1
                else:
                    cdcount += 1
                if verbLevel >= 3:
                    ofile.write("c Was: %s\n" % line)
            sfields = [str(val) for val in nfields]
            if cmd == 'a':
                ofile.write("%d a %s\n" % (id, " ".join(sfields)))
            elif cmd == 'dc':
                ofile.write("dc %d %s\n" % (id, " ".join(sfields)))
            else:
                raise Exception("Unknown CRAT command '%s'" % str(cmd))

    if verbLevel >= 1:
        print("HINTIFY: %d unhinted assertions --> %d hinted assertions" % (dacount, aacount))
        print("HINTIFY: %d unhinted deletions --> %d hinted deletions" % (ddcount, adcount))
        print("HINTIFY: %d assertions, %d deletions with changed hints" % (cacount, cdcount))
    ifile.close()
    ofile.close()

def run(name, args):
    global acnfName, dratName, lratName
    cnfName = None
    cratName = None
    hcratName = None
    splitMode = 1
    verbLevel = 1
    optList, args = getopt.getopt(args, "hs:v:i:p:o:v:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-s':
            splitMode = int(val)
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
    dratName = root + ".drat"
    acnfName = root + ".acnf"
    lratName = root + ".lrat"

    t0 = datetime.datetime.now()
    splitFiles(cnfName, cratName, verbLevel)
    t1 = datetime.datetime.now()
    if splitMode == 1:
        genHints(verbLevel)
        t2 = datetime.datetime.now()
        insertHintsMode1(cratName, hcratName, verbLevel)
        t3 = datetime.datetime.now()
    else:
        justifyAssertions(verbLevel)
        t2 = datetime.datetime.now()
        insertHintsMode2(cratName, hcratName, verbLevel)
        t3 = datetime.datetime.now()        
    d1 = t1 - t0
    d2 = t2 - t1
    d3 = t3 - t2
    d  = t3 - t0
    s1 = d1.seconds + 1e-6 * d1.microseconds
    s2 = d2.seconds + 1e-6 * d2.microseconds
    s3 = d3.seconds + 1e-6 * d3.microseconds
    s  = d.seconds  + 1e-6 * d.microseconds
    if splitMode == 1:
        dstring = "HINTIFY: Elapsed seconds for hint addition: %.2f split files + %.2f DRAT-TRIM + %.2f insert hints = %.2f"
    else:
        dstring = "HINTIFY: Elapsed seconds for hint generation: %.2f split files + %.2f justify/DRAT-TRIM + %.2f insert hints = %.2f"
    print(dstring % (s1, s2, s3, s))


    if deleteTempFiles:
        for tname in tmpList:
            try:
                os.remove(tname)
            except:
                continue

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
