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

# Input:
# CNF file (augmented from original)
#  a "proto-DRAT" file consisting of clause assertions and deletions, where the assertions are unproven
#  expand each assertion into a sequence of proof steps
# Then run through DRAT-TRIM to get LRAT file

import sys
import os
import getopt
import subprocess
import datetime
import readwrite
from pysat.solvers import Solver

def usage(name):
    print("Usage: %s [-h] [-v VLEVEL] -i FILE.cnf -d IFILE.drat -o OFILE.lrat")
    print(" -h              Print this message")
    print(" -v VLEVEL       Set verbosity level (0-3)")
    print(" -i FILE.cnf     Input CNF")
    print(" -d IFILE.drat   Input DRAT")
    print(" -o FILE.drat    Output LRAT")

class JustifierException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Justifier Exception: " + str(self.value)


# Where is DRAT-TRIM?
path = os.path.dirname(os.path.realpath(__file__)) + "/crat-lrat"
prog = path + "/" + "crat-lrat"

# Debugging options
deleteTempFiles = False

# Use glucose4 as solver
solverId = 'g4'

# Wrapper around SAT solver
# Operates in two phases.
# During first, process clause deletions
# During second, convert asserted clauses into proof steps
# Proof steps get accumulated within solver.  Dump out at end

class Justifier:
    inputClauseList = []
    solver = None
    verbLevel = 1
    ## Statistics
    initialInputClauseCount = 0
    compressedInputClauseCount = 0
    # Number of proof steps, indexed by number of clauses to justify assertion
    proofClauseCounts = {}

    def __init__(self, inputClauseList, verbLevel = 1):
        # Make copy so that can mutate
        self.inputClauseList = list(inputClauseList)
        self.solver = None
        self.verbLevel = verbLevel
        self.initialInputClauseCount = len(inputClauseList)
        self.compressedInputClauseCount = 0
        self.proofClauseCounts = {}
        
    ### Phase 1 capabilities
    def setupSolver(self):
        if self.solver is not None:
            raise JustifierException("Cannot set up solver.  Already exists")
        self.solver = Solver(solverId, with_proof = True)
        # Compress the clause list
        icount = len(self.inputClauseList)
        self.inputClauseList = [clause for clause in self.inputClauseList if clause is not None]
        self.solver.append_formula(self.inputClauseList)
        self.compressedInputClauseCount = len(self.inputClauseList)
        if self.verbLevel >= 3:
            icount = self.initialInputClauseCount
            ncount = self.compressedInputClauseCount
            print("Justifier: Set up solver.  Original %d input clauses --> %d clauses after deletions" % (icount, ncount))

    def deleteClause(self, dclause):
        if self.solver is not None:
            raise JustifierException("Cannot delete clause.  Solver already exists")
        # Work from back to front
        N = len(self.inputClauseList)
        for rid in range(N):
            cid = N-rid-1
            iclause = self.inputClauseList[cid]
            if iclause is None:
                continue
            if readwrite.testClauseEquality(dclause, iclause):
                if self.verbLevel >= 3:
                    print("Justifier: Deleted clause #%d %s" % (cid, str(iclause)))
                self.inputClauseList[cid] = None
                return True
        if self.verbLevel >= 3:
            print("Justifier: Couldn't find clause %s to delete" % str(dclause))
        return False

    ### Phase 2 capabilities

    def justifyClause(self, tclause):
        if self.solver is None:
            self.setupSolver()
        assumptions = readwrite.invertClause(tclause)
        sstate = self.solver.solve(assumptions = assumptions)
        ok = not sstate
        if self.verbLevel >= 3:
            if ok:
                print("Justifier: Justified clause %s" % str(tclause))
            else:
                print("Justifier: Failed to justify clause %s" % str(tclause))
        return ok
        
    # Extract clause from string
    # Return None if clause deletion
    # Raises exception if something else goes wrong
    def strToClause(self, sclause):
        sfields = sclause.split()
        if len(sfields) > 0 and sfields[0] == 'd':
            # Ignore deletions
            return None
        try:
            fields = [int(s) for s in sfields]
        except:
            raise JustifierException("Proof failure.  SAT solver returned invalid proof clause %s" % sclause)
        if len(fields) == 0 or fields[-1] != 0:
            raise JustifierException("Proof failure.  SAT solver returned invalid proof clause %s" % sclause)
        clause = fields[:-1]
        return clause


    def getClauseFromList(self, slist):
        while len(slist) > 0:
            sclause = slist[0]
            slist = slist[1:]
            clause = self.strToClause(sclause)
            if clause is not None:
                return clause, slist
        return None, slist

    # Reread contents of DRAT file, so that can emit deletions
    # and match assertions with their proofs
    def emitDrat(self, inDratName, owriter):
        ireader = readwrite.DratReader(inDratName)
        dcount = 0
        acount =  0
        slist = self.solver.get_proof()
        while True:
            (key, dclause) = ireader.readStep()
            if key is None:
                break
            elif key == 'd':
                owriter.doDelete(dclause)
                dcount += 1
                continue
            # Assertion
            acount += 1
            pclause = None
            plength = 0
            while True:
                aclause, slist = self.getClauseFromList(slist)
                if aclause is None:
                    raise JustifierException("Ran out of proof steps trying to justify assertion #%d: %s" % (acount, str(aclause)))
                if len(aclause) == 0:
                    # Terminator
                    if pclause is None or pclause != dclause:
                        owriter.doStep(dclause)
                        plength += 1
                    break
                owriter.doStep(aclause)
                plength += 1
                pclause = aclause
            if plength in self.proofClauseCounts:
                self.proofClauseCounts[plength] += 1
            else:
                self.proofClauseCounts[plength] = 1
        ireader.finish()
        owriter.finish()
        if self.verbLevel >= 1:
            print("JUSTIFY: %d input clauses --> %d after deletions" % (self.initialInputClauseCount, self.compressedInputClauseCount))
            print("JUSTIFY: Input DRAT %d deletions, %d assertions" % (dcount, acount))
            print("JUSTIFY: Proof step counts (by number of clauses in proof:")
            singletons = []
            nscount = 0
            for count in sorted(self.proofClauseCounts.keys()):
                nc = self.proofClauseCounts[count]
                nscount += count * nc
                if nc == 1:
                    singletons.append(str(count))
                else:
                    print("JUSTIFY:    %d : %d" % (count, nc))
            if len(singletons) > 1:
                print("JUSTIFY:    1 each for counts %s" % ", ".join(singletons))
            print("JUSTIFY:    TOTAL: %d" % nscount)


    

# Make up a name for intermediate files
def getRoot(cnfName):
    prefix = "tmp_"
    fields = cnfName.split(".")
    if len(fields) > 0:
        fields = fields[:-1]
    fields[0] = prefix + fields[0]
    return ".".join(fields)

# Convert file containing clause deletions and assertions into
# one with deletions + proof steps.  Both use DRAT format
def expandDrat(cnfName, inDratName, outDratName, verbLevel):
    cnfReader = readwrite.CnfReader(cnfName, verbLevel)
    dratReader = readwrite.DratReader(inDratName, verbLevel)
    dratWriter = readwrite.DratWriter(outDratName, verbLevel)
    justifier = Justifier(cnfReader.clauses, verbLevel)

    # First part: Process input DRAT file, consisting of clause deletions followed by assertions
    # Pass deletions to output DRAT file and accumulate assertion proofs within justifier
    while True:
        (key, clause) = dratReader.readStep()
        if key is None:
            break
        elif key == 'a':
            if not justifier.justifyClause(clause):
                raise JustifierException("Justification failed.  Could not justify clause '%s'" % str(clause))
        elif key == 'd':
            if not justifier.deleteClause(clause):
                raise JustifierException("Clause deletion failed.  Could find clause '%s'" % str(clause))
            dratWriter.doDelete(clause)
        else:
            raise JustifierException("Internal error.  Don't recognize key '%s'" % str(key))
    dratReader.finish()

    # Second part: Add proof steps to output DRAT file
    justifier.emitDrat(inDratName, dratWriter)
    dratWriter.finish()

def fixLine(line):
    line = line.decode('utf-8')
    while len(line) > 0 and line[0] in ' \n\r':
        line = line[1:]
    while len(line) > 0 and line[-1] in ' \n\r':
        line = line[:-1]
    return line

def genLrat(cnfName, dratName, lratName, verbLevel):
    args = [prog, cnfName, dratName, "-f"]
    proc = subprocess.Popen(args, stdout=subprocess.PIPE)
    try:
        lfile = open(lratName, 'w')
    except:
        print("Couldn't open LRAT file '%s'" % lratName)
        sys.exit(1)

    for line in proc.stdout:
        line = fixLine(line)
        if len(line) == 0 or line[0] == 'c':
            continue
        if line[-1] != '0':
            continue
        lfile.write(line + '\n')
    lfile.close()

def run(name, args):
    tmpList  = []
    cnfName = None
    dratName = None
    lratName = None
    verbLevel = 1
    optList, args = getopt.getopt(args, "hv:i:d:o:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-d':
            dratName = val
        elif opt == '-o':
            lratName = val
        else:
            usage(name)
            return
    if cnfName is None or dratName is None or lratName is None:
        print("Require names for CNF file input DRAT file, and output LRAT file")
        usage(name)
        return
    root = getRoot(cnfName)
    expandedDratName = root + ".expanded_drat"
    tmpList.append(expandedDratName)
    t0 = datetime.datetime.now()
    expandDrat(cnfName, dratName, expandedDratName, verbLevel)
    t1 = datetime.datetime.now()
    genLrat(cnfName, expandedDratName, lratName, verbLevel)
    t2 = datetime.datetime.now()
    if deleteTempFiles:
        for tname in tmpList:
            try:
                os.remove(tname)
            except:
                continue
    d1 = t1 - t0
    d2 = t2 - t1
    d  = t2 - t0
    s1 = d1.seconds + 1e-6 * d1.microseconds
    s2 = d2.seconds + 1e-6 * d2.microseconds
    s  = d.seconds  + 1e-6 * d.microseconds
    print("JUSTIFY: Elapsed seconds for justifications: %.2f expand DRAT + %.2f DRAT-TRIM = %.2f" %
          (s1, s2, s))

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
