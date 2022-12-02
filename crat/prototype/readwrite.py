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

import os
import sys

class ReadWriteException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "ReadWrite Exception: " + str(self.value)

# Code for reading and generating CNF, order, schedule, and crat proof files

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def addPrefix(path, prefix):
    pfields = path.split("/")
    pfields[-1] = prefix + pfields[-1]
    return "/".join(pfields)

tautologyId = 1000 * 1000 * 1000

# Clean up clause.
# Remove duplicates
# Sort in reverse order of variable number
# Don't allow clause to have opposite literals (returns tautologyId)
def cleanClause(literalList):
    slist = sorted(literalList, key = lambda v: abs(v))
    if len(slist) == 0:
        return tuple(slist)
    if slist[0] == tautologyId:
        return tautologyId
    if slist[0] == -tautologyId:
        slist = slist[1:]
        if slist[0] == tautologyId:
            return tautologyId
    if len(slist) == 1:
        return tuple(slist)
    nlist = [slist[0]]
    for i in range(1, len(slist)):
        if slist[i-1] == slist[i]:
            continue
        if slist[i-1] == -slist[i]:
            return tautologyId
        nlist.append(slist[i])
    return tuple(nlist)

# Fix up set of input clauses
# Flag error if any tautologies
def cleanClauses(clist):
    nlist = []
    id = 0
    for clause in clist:
        id += 1
        nclause = cleanClause(clause)
        if nclause == tautologyId:
            raise ReadWriteException("Tautologous clause #%d: %s" % (id, str(clause)))
        nlist.append(nclause)
    return nlist

## Clause for supporting clause testing
class ClauseChecker:
    # Generation counter
    generation = 1
    maxVariable = 0
    # Arrays, indexed by variable
    # Indicate last generation for which literal occurred positively & negatively
    occurPos = [0]
    occurNeg = [0]

    def __init__(self, maxVariable = 1):
        self.maxVariable = 0
        self.getReady(maxVariable)

    def getReady(self, maxVariable):
        if maxVariable <= self.maxVariable:
            self.generation += 1
            return
        self.generation = 1
        self.occurPos = [0] * (maxVariable + 1)
        self.occurNeg = [0] * (maxVariable + 1)
        self.maxVariable = maxVariable

    def mark(self, lit):
        if lit > 0:
            self.occurPos[lit] = self.generation
        else:
            self.occurNeg[-lit] = self.generation

    def checkMark(self, lit):
        if lit > 0:
            return self.occurPos[lit] == self.generation
        else:
            return self.occurNeg[-lit] == self.generation
        

    def subsetTest(self, clause1, clause2):
        if len(clause1) > len(clause2):
            return False
        m1 = max([abs(lit) for lit in clause1])
        m2 = max([abs(lit) for lit in clause2])
        self.getReady(max(m1, m2))
        for lit in clause2:
            self.mark(lit)
        ok = True
        for lit in clause1:
            if not self.checkMark(lit):
                ok = False
                break
        return ok
            
    def equalityTest(self, clause1, clause2):
        if len(clause1) != len(clause2):
            return False
        return self.subsetTest(clause1, clause2)
        
checker = None        
        
        
# Test two clauses for equality.  Assumes syntactically equivalent
def oldTestClauseEquality(clause1, clause2, quick = False):
       
    if clause1 is None or clause2 is None:
        return False
    if clause1 == tautologyId and clause2 == tautologyId:
        return True
    if len(clause1) != len(clause2):
        return False
    if not quick:
        clause1 = cleanClause(clause1)
        clause2 = cleanClause(clause2)
    for l1,l2 in zip(clause1, clause2):
        if l1 != l2:
            return False
    return True

# Clause comparison.  Assumes both have been processed by cleanClause
def oldTestClauseSubset(clause1, clause2):
    if clause1 is None or clause2 is None:
        return False
    if clause2 == tautologyId:
        return True
    if clause1 == tautologyId:
        return False
    idx1 = 0
    idx2 = 0
    while idx1 < len(clause1):
        if idx2 >= len(clause2):
            return False
        head1 = clause1[idx1]
        head2 = clause2[idx2]
        if abs(head1) > abs(head2):
            idx2 += 1
        elif abs(head1) < abs(head2):
            return False
        elif head1 == head2:
            idx1 += 1
            idx2 += 1
        else:
            return False
    return True


# Test two clauses for equality.  
def testClauseEquality(clause1, clause2):
    global checker
    if checker is None:
        checker = ClauseChecker()
    rnew = checker.equalityTest(clause1, clause2)
    return rnew
#    rold = oldTestEquality(clause1, clause2)
#    if rnew != rold:
#        print("Mismatch testing equality of clauses %s and %s.  Old = %s, New = %s" % (str(clause1), str(clause2), str(rold), str(rnew)))
#    return rold

            

# Clause comparison.  
def testClauseSubset(clause1, clause2):
    global checker
    if checker is None:
        checker = ClauseChecker()
    rnew = checker.subsetTest(clause1, clause2)
    return rnew
#    rold = oldTestSubset(clause1, clause2)
#    return rold
#    if rnew != rold:
#        print("Mismatch testing clause %s subset of %s.  Old = %s, New = %s" % (str(clause1), str(clause2), str(rold), str(rnew)))
#    return rold


def regularClause(clause):
    return clause is not None

def showClause(clause):
    if clause is None:
        return "NONE"
    return str(clause)

# Return inverted set of literals
def invertClause(literalList):
    if literalList == tautologyId:
        return []
    else:
        return [-lit for lit in literalList]


# Eliminate any falsified literals
# If some literal satisfied, return tautology
def unitReduce(clause, unitSet):
    if clause == tautologyId:
        return clause
    nclause = []
    for lit in clause:
        if lit in unitSet:
            return tautologyId
        elif -lit not in unitSet:
            nclause.append(lit)
    return nclause


# Read CNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class CnfReader():
    file = None
    commentLines = []
    clauses = []
    nvar = 0
    verbLevel = 1

   
    def __init__(self, fname = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            opened = True
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise ReadWriteException("Could not open file '%s'" % fname)
        self.clauses = []
        self.commentLines = []
        try:
            self.readCnf()
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        if opened:
            self.file.close()
        
    def readCnf(self):
        lineNumber = 0
        nclause = 0
        self.nvar = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            fields = line.split()
            if len(fields) == 0:
                continue
            elif line[0] == 'c':
                if self.verbLevel > 1:
                    self.commentLines.append(line)
            elif line[0] == 'p':
                fields = line[1:].split()
                if len(fields) != 3 or fields[0] != 'cnf':
                    raise ReadWriteException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise ReadWriteException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
            else:
                if nclause == 0:
                    raise ReadWriteException("Line %d.  No header line.  Not cnf" % (lineNumber))
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    raise ReadWriteException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if lits[-1] != 0:
                    raise ReadWriteException("Line %d.  Clause line should end with 0" % lineNumber)
                lits = lits[:-1]
                vars = sorted([abs(l) for l in lits])
                if len(vars) == 0:
                    raise ReadWriteException("Line %d.  Empty clause" % lineNumber)                    
                if vars[-1] > self.nvar or vars[0] == 0:
                    raise ReadWriteException("Line %d.  Out-of-range literal" % lineNumber)
                for i in range(len(vars) - 1):
                    if vars[i] == vars[i+1]:
                        raise ReadWriteException("Line %d.  Opposite or repeated literal" % lineNumber)
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            raise ReadWriteException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
        self.file.close()

# Grab list of clauses out of file that may contain other info
# Interesting lines will contain marker and have list of literals following that
class ClauseReader():

    file = None
    clauses = []
    verbLevel = 1
    marker = ""
    lineNumber = 0

    def __init__(self, fname = None, marker = "", verbLevel = 1):
        self.marker = marker
        self.verbLevel = verbLevel
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            opened = True
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise ReadWriteException("Could not open file '%s'" % fname)
        self.clauses = []
        self.lineNumber = 0

    def readClause(self):
        found = False
        clause = None
        for line in self.file:
            self.lineNumber += 1
            if self.marker not in line:
                continue
            line = trim(line)
            fields = line.split()
            if len(fields) == 0:
                continue
            if self.marker != "":
                pos = -1
                for ipos in range(len(fields)):
                    if fields[ipos] == self.marker:
                        pos = ipos
                        break
                if pos < 0:
                    raise ReadWriteException("Line #%d.  Marker '%s' not isolated in line '%s'" % (self.lineNumber, self.marker, line))
                fields = fields[pos+1:]
            try:
                lits = [int(f) for f in fields]
            except:
                raise ReadWriteException("Line #%d.  Non-integer literal in line '%s'" % (self.lineNumber, line))
            if len(lits) == 0:
                continue
            if lits[-1] != 0:
                raise ReadWriteException("Line #%d.  List of literals must be terminated by 0. Line = '%s'" % (self.lineNumber, line))
            lits = lits[:-1]
            found = True
            clause = lits
            break
        return (found, clause)


    def readClauses(self):
        self.clauses = []
        while True:
            (found, clause) = self.readClause()
            if not found:
                break
            self.clauses.append(clause)
        if self.verbLevel >= 1:
            print("Clause reader read %d clauses" % len(self.clauses))

# Grab list of clauses out of file that may contain other info
# Interesting lines will contain marker and have list of literals following that
class DratReader():

    file = None
    verbLevel = 1
    lineNumber = 0


    def __init__(self, fname = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise ReadWriteException("Could not open file '%s'" % fname)
            opened = True
        self.lineNumber = 0

    # Read addition or deletion step
    # Return (key, clause)
    # Where key is 'a', 'd', or None
    def readStep(self):
        key = None
        clause = None
        for line in self.file:
            self.lineNumber += 1
            line = trim(line)
            fields = line.split()
            if len(fields) == 0 or fields[0] == 'c':
                continue
            if fields[0] == 'd':
                key = 'd'
                fields = fields[1:]
            else:
                key = 'a'
            try:
                lits = [int(f) for f in fields]
            except:
                raise ReadWriteException("Line #%d.  Non-integer literal in line '%s'" % (self.lineNumber, line))
            if len(lits) == 0:
                continue
            if lits[-1] != 0:
                raise ReadWriteException("Line #%d.  List of literals must be terminated by 0. Line = '%s'" % (self.lineNumber, line))
            clause = lits[:-1]
            break
        return (key, clause)

    def finish(self):
        self.file.close()

# Read lines from LRAT file
class LratReader():

    file = None
    verbLevel = 1
    lineNumber = 0

    def __init__(self, fname = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise ReadWriteException("Could not open file '%s'" % fname)
            opened = True
        self.lineNumber = 0

    # Read addition or deletion step
    # Return (key, id, clause, hints)
    # key = 'a' for addition, 'd' for deletion, and None for end of file
    def readStep(self):
        key = None
        id = 0
        clause = []
        hints = []
        fields = []
        for line in self.file:
            self.lineNumber += 1
            line = trim(line)
            fields = line.split()
            if len(fields) > 0 and fields[0] != 'c' and fields[0] != 's':
                break
        if len(fields) == 0 or fields[0] == 'c':
            return (key, id, clause, hints)
        try:
            id = int(fields[0])
            fields = fields[1:]
        except:
            raise ReadWriteException("Line #%d.  Couldn't extract clause Id from line '%s'" % (self.lineNumber, line))
        if len(fields) >= 1 and fields[0] == 'd':
            key = 'd'
            fields = fields[1:]
        else:
            key = 'a'
        try:
            vals = [int(f) for f in fields]
        except:
            raise ReadWriteException("Line #%d.  Non-integer literal in line '%s'" % (self.lineNumber, line))
        gotClause = False
        gotHints = False
        for v in vals:
            if v == 0:
                if not gotClause:
                    gotClause = True
                elif not gotHints:
                    gotHints = True
                else:
                    ReadWriteException("Line #%d.  Too many 0's in line '%s'" % (self.lineNumber, line))
            else:
                if not gotClause:
                    clause.append(v)
                elif not gotHints:
                    hints.append(v)
                else:
                    ReadWriteException("Line #%d.  Value beyond second zero in line '%s'" % (self.lineNumber, line))
        if not gotClause:
            ReadWriteException("Line #%d.  Couldn't extract literals in line '%s'" % (self.lineNumber, line))
        if not gotHints:
            ReadWriteException("Line #%d.  Couldn't extract hints in line '%s'" % (self.lineNumber, line))
        return (key, id, clause, hints)

    def finish(self):
        self.file.close()


# Generic writer
class Writer:
    outfile = None
    verbLevel = 1
    expectedVariableCount = None
    isNull = False
    fname = ""

    def __init__(self, count, fname, verbLevel = 1, isNull = False):
        self.expectedVariableCount = count
        self.fname = fname
        self.verbLevel = verbLevel
        self.isNull = isNull
        self.fname = fname
        if isNull:
            return
        try:
            self.outfile = open(fname, 'w')
        except:
            print("Couldn't open file '%s'. Aborting" % fname)
            sys.exit(1)

    def vcount(self):
        return self.expectedVariableCount

    def show(self, line):
        if self.isNull:
            return
        line = trim(line)
        if self.verbLevel > 2:
            print(line)
        if self.outfile is not None:
            self.outfile.write(line + '\n')

    def finish(self):
        if self.isNull:
            return
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None


class DratWriter(Writer):
    additions = 0
    deletions = 0

    def __init__(self, fname, verbLevel=1):
        Writer.__init__(self, 0, fname, verbLevel=verbLevel)
        self.additions = 0
        self.deletions = 0

    def doStep(self, lits):
        slits = [str(lit) for lit in lits] + ['0']
        line = " ".join(slits)
        self.show(line)
        self.additions += 1

    def doDelete(self, lits):
        slits = ['d'] + [str(lit) for lit in lits] + ['0']
        line = " ".join(slits)
        self.show(line)
        self.deletions += 1

# Creating CNF
class CnfWriter(Writer):
    clauseCount = 0
    outputList = []
    # Track which variables actually occur
    vset = set([])

    def __init__(self, count, fname, verbLevel = 1):
        Writer.__init__(self, count, fname, verbLevel = verbLevel)
        self.clauseCount = 0
        self.outputList = []
        self.vset = set([])

    # With CNF, must accumulate all of the clauses, since the file header
    # requires providing the number of clauses.

    def doComment(self, line):
        self.outputList.append("c " + line)

    def doClause(self, literals):
        for lit in literals:
            var = abs(lit)
            if var <= 0 or var > self.expectedVariableCount:
                raise ReadWriteException("Variable %d out of range 1--%d" % (var, self.expectedVariableCount))
            self.vset.add(var)
        ilist = literals + [0]
        self.outputList.append(" ".join([str(i) for i in ilist]))
        self.clauseCount += 1
        return self.clauseCount

    def variableCount(self):
        return len(self.vset)

    def finish(self, incremental = False):
        if self.isNull:
            return
        if self.outfile is None:
            return
        if incremental:
            self.show("p inccnf")
        else:
            self.show("p cnf %d %d" % (self.expectedVariableCount, self.clauseCount))
        for line in self.outputList:
            self.show(line)
        self.outfile.close()
        self.outfile = None


# Version that allows adding clauses for product operators
class AugmentedCnfWriter(CnfWriter):
    
    cubeCount = 0
    tautologyCount = 0

    def __init__(self, count, fname, verbLevel = 1):
        CnfWriter.__init__(self, count, fname, verbLevel)
        self.cubeCount = 0
        self.tautologyCount = 0


    # Optionally have the DRAT file delete all but the first clause
    def doProduct(self, var, args, dwriter = None, firstClauseOnly = False):
        self.expectedVariableCount = max(self.expectedVariableCount, var)
        lits = [var] + [-arg for arg in args]
        id = self.doClause(lits)
        for arg in args:
            if firstClauseOnly:
                # Insert tautology as placeholder
                lits = [-var, var]
                self.tautologyCount += 1
            else:
                lits = [-var, arg]
            self.doClause(lits)
            if dwriter is not None:
                dwriter.doDelete(lits)
        return id

    def doCube(self, lits):
        slits = [str(-lit) for lit in lits] + ['0']
        line = "a " + " ".join(slits)
        self.outputList.append(line)
        self.cubeCount += 1


# Enable permuting of variables before emitting CNF
class Permuter:
    forwardMap = {}
    reverseMap = {}
    
    def __init__(self, valueList = [], permutedList = []):
        self.forwardMap = {}
        self.reverseMap = {}
        identity = False
        if len(permutedList) == 0:
            permutedList = valueList
            identity = True
        if len(valueList) != len(permutedList):
            raise ReadWriteException("Unequal list lengths: %d, %d" % (len(valueList), len(permutedList)))
        for v, p in zip(valueList, permutedList):
            self.forwardMap[v] = p
            self.reverseMap[p] = v
        if identity:
            return
        # Check permutation
        for v in valueList:
            if v not in self.reverseMap:
                raise ReadWriteException("Not permutation: Nothing maps to %s" % str(v))
        for v in permutedList:
            if v not in self.forwardMap:
                raise ReadWriteException("Not permutation: %s does not map anything" % str(v))
            
            
    def forward(self, v):
        if v not in self.forwardMap:
            raise ReadWriteException("Value %s not in permutation" % (str(v)))
        return self.forwardMap[v]

    def reverse(self, v):
        if v not in self.reverseMap:
            raise ReadWriteException("Value %s not in permutation range" % (str(v)))
        return self.reverseMap[v]
    
    def __len__(self):
        return len(self.forwardMap)


# Creating CNF incrementally.  Don't know number of variables in advance
class LazyCnfWriter:

    variableCount = 0
    # Set of tuples (T/F, item)
    # Boolean T for clause F for comment
    # item: list of literals for clause, string for comment
    items = []
    fname = ""
    verbLevel = 1
    permuter = None

    def __init__(self, fname, permuter = None, verbLevel = 1):
        self.variableCount = 0
        self.items = []
        self.fname = fname
        self.permuter = permuter
        self.verbLevel = verbLevel


    def newVariable(self):
        self.variableCount += 1
        if self.permuter is not None:
            return self.permuter.reverse(self.variableCount)
        else:
            return self.variableCount

    def vcount(self):
        return self.variableCount

    def newVariables(self, n):
        return [self.newVariable() for i in range(n)]
    
    def doComment(self, line):
        self.items.append((False, line))

    def doClause(self, lits):
        self.items.append((True, lits))

    def clauseList(self):
        clist = []
        for (isClause, value) in self.items:
            if isClause:
                clist.append(value)
        return clist

    def finish(self):
        writer = CnfWriter(self.variableCount, self.fname, self.verbLevel)
        for (isClause, value) in self.items:
            if isClause:
                writer.doClause(value)
            else:
                writer.doComment(value)
        writer.finish()
        print("c File '%s' has %d variables and %d clauses" % (self.fname, self.variableCount, writer.clauseCount))

# Creating LRAT proof
class LratWriter(Writer):

    # Must initialize this to the number of clauses in the original CNF file
    clauseCount = 0

    def __init__(self, clauseCount, fname, verbLevel = 1):
        Writer.__init__(self, None, fname, verbLevel = verbLevel)
        self.clauseCount = clauseCount

    def doComment(self, line):
        self.show("c " + line)

    def doStep(self, lits, ids):
        self.clauseCount += 1
        ilist = [self.clauseCount] + lits + [0] + ids + [0]
        self.show(" ".join([str(i) for i in ilist]))
        return self.clauseCount
     
    
class ScheduleWriter(Writer):
    # Track potential errors
    stackDepth = 0
    decrementAnd = False
    expectedFinal = 1

    def __init__(self, count, fname, verbLevel = 1, isNull = False):
        Writer.__init__(self, count, fname, verbLevel = verbLevel, isNull = isNull)
        self.stackDepth = 0
        self.decrementAnd = False
    
    def getClauses(self, clist):
        self.show("c %s" % " ".join([str(c) for c in clist]))
        self.stackDepth += len(clist)

    # First time with new tree, want one fewer and operations
    def newTree(self):
        self.decrementAnd = True

    def doAnd(self, count):
        if self.decrementAnd:
            count -= 1
        self.decrementAnd = False
        if count == 0:
            return
        if count+1 > self.stackDepth:
            print("Warning: Cannot perform %d And's.  Only %d elements on stack" % (count, self.stackDepth))
        self.show("a %d" % count)
        self.stackDepth -= count

    def doStore(self, name):
        self.show("s %s" % name)

    def doRetrieve(self, name):
        self.show("r %s" % name)

    def doDelete(self, name):
        self.show("d %s" % name)

    def doEquality(self):
        self.show("e")

    def doQuantify(self, vlist):
        if self.isNull:
            return
        if self.stackDepth == 0:
            print ("Warning: Cannot quantify.  Stack empty")
#            raise ReadWriteException("Cannot quantify.  Stack empty")
        self.show("q %s" % " ".join([str(c) for c in vlist]))

    # Issue equation or constraint.
    def doPseudoBoolean(self, vlist, clist, const, isEquation=True):
        if self.isNull:
            return
        # Anticipate that shifting everything from CNF evaluation to pseudoboolean reasoning
        self.expectedFinal = 0
        if self.stackDepth == 0:
            print ("Warning: Cannot quantify.  Stack empty")
        if len(vlist) != len(clist):
            raise ReadWriteException("Invalid equation or constraint.  %d variables, %d coefficients" % (len(vlist), len(clist)))
        cmd = "=" if isEquation else ">="
        slist = [cmd, str(const)]
        slist += [("%d.%d" % (c,v)) for (c,v) in zip(clist, vlist)]
        self.show(" ".join(slist))
        self.stackDepth -= 1

    def doComment(self, cstring):
        self.show("# " + cstring)

    def doInformation(self, cstring):
        self.show("i " + cstring)

    def finish(self):
        if self.isNull:
            return
        if self.stackDepth != self.expectedFinal:
            print("Warning: Invalid schedule.  Finish with %d elements on stack" % self.stackDepth)
#            raise ReadWriteException("Invalid schedule.  Finish with %d elements on stack" % self.stackDepth)
        Writer.finish(self)

class OrderWriter(Writer):
    variableList = []

    def __init__(self, count, fname, verbLevel = 1, isNull = False):
        Writer.__init__(self, count, fname, verbLevel = verbLevel, isNull = isNull)
        self.variableList = []

    def doOrder(self, vlist):
        self.show(" ".join([str(c) for c in vlist]))        
        self.variableList += vlist

    def finish(self):
        if self.isNull:
            return
        if self.expectedVariableCount != len(self.variableList):
#            raise ReadWriteException("Incorrect number of variables in ordering %d != %d" % (
#                len(self.variableList), self.expectedVariableCount))
            print("Warning: Incorrect number of variables in ordering")
            print("  Expected %d.  Got %d" % (self.expectedVariableCount, len(self.variableList)))

        expected = range(1, self.expectedVariableCount+1)
        self.variableList.sort()
        for (e, a) in zip(expected, self.variableList):
            if e != a:
               raise ReadWriteException("Mismatch in ordering.  Expected %d.  Got %d" % (e, a))
        print("c File '%s' written" % (self.fname))
        Writer.finish(self)


class SplitWriter(Writer):
    upperOutfile = None
    isSplit = False
    ufname = ""

    def __init__(self, count, fname, verbLevel = 1, isNull = False):
        Writer.__init__(self, count, fname, verbLevel = 1, isNull = False)
        self.upperOutfile = None
        self.isSplit = False
        self.ufname = ""

    def split(self):
        self.ufname = addPrefix(self.fname, "upper_")
        try:
            self.upperOutfile = open(self.ufname, 'w')
        except:
            raise ReadWriteException("Couldn't open supplementary file '%s' when splitting" % self.ufname)
        self.isSplit = True

    def show(self, line, splitLower = False):
        if self.isSplit and not splitLower:
            line = trim(line)
            if self.verbLevel > 2:
                print(line)
            self.upperOutfile.write(line + '\n')
        else:
            Writer.show(self, line)

    def finish(self):
        if self.isSplit:
            self.upperOutfile.close()
            try:
                infile = open(self.ufname, 'r')
            except:
                raise ReadWriteException("Couldn't open supplementary file '%s' when merging files")
            for line in infile:
                Writer.show(self, line)
            infile.close()
            try:
                os.remove(self.ufname)
            except:
                raise ReadWriteException("Couldn't delete supplementary file '%s'" % self.ufname)
        Writer.finish(self)

# Where should split proofs start their upper steps
upperStepStart = 100 * 1000 * 1000

class CratWriter(SplitWriter):
    variableCount = 0
    usedVariableSet = set([])
    clauseDict = []
    lowerStepCount = 0
    upperStepCount = upperStepStart
    # Maintain lists of clause additions.  Each is tuple of form (id, hints)
    lowerHintStack = []
    upperHintStack = []

    def __init__(self, variableCount, clauseList, fname, verbLevel = 1):
        Writer.__init__(self, variableCount, fname, verbLevel=verbLevel, isNull=False)
        self.variableCount = variableCount
        self.usedVariableSet = set([])
        self.lowerStepCount = len(clauseList)
        self.upperStepCount = upperStepStart
        self.clauseDict = {}
        self.lowerClauseStack = []
        self.upperClauseStack = []

        if verbLevel >= 2 and len(clauseList) > 0:
            self.doComment("Input clauses")
        for s in range(1, len(clauseList)+1):
            lits = clauseList[s-1]
            if verbLevel >= 2:
                self.doLine(['c', s, 'i'] + lits + [0])
            self.addClause(s, lits)

    def incrStep(self, delta = 1, splitLower = False):
        if self.isSplit and not splitLower:
            cid = self.upperStepCount
            self.upperStepCount += delta
        else:
            cid = self.lowerStepCount
            self.lowerStepCount += delta
        return cid+1

    def addClause(self, step, lits):
        for lit in lits:
            self.usedVariableSet.add(abs(lit))
        self.clauseDict[step] = lits
        print("Added clause #%d %s" % (step, lits))

    def deleteClause(self, step):
        del self.clauseDict[step]
        print("Deleted clause #%d" % step)

    def doLine(self, items, splitLower = False):
        slist = [str(i) for i in items]
        self.show(" ".join(slist), splitLower)

    def doComment(self, line, splitLower = False):
        self.show("c " + line, splitLower)
        
    def newXvar(self):
        self.variableCount += 1
        v = self.variableCount
        return v

    def finalizeAnd(self, ilist, xvar):
        step = self.incrStep()
        self.doLine([step, 'p', xvar] + ilist + [0])
        cpos = [xvar] + [-i for i in ilist]
        self.addClause(step, cpos)
        if self.verbLevel >= 2:
            self.doComment("Implicit declarations:")
            slist = [str(lit) for lit in cpos]
            self.doComment("%d a %s 0" % (step, " ".join(slist)))
        for idx in range(len(ilist)):
            self.addClause(step+idx+1, [-xvar, ilist[idx]])
            if self.verbLevel >= 2:
                self.doComment("%d a %d %d 0" % (step+1+idx, -xvar, ilist[idx]))
        self.incrStep(len(ilist))
        return step

    def finalizeOr(self, ilist, xvar, hints):
        if hints is None:
            hints = ['*']
        step = self.incrStep()
        i1 = ilist[0]
        i2 = ilist[1]
        self.doLine([step, 's', xvar, i1, i2] + hints + [0])
        self.addClause(step, [-xvar, i1, i2])
        self.addClause(step+1, [xvar, -i1])        
        self.addClause(step+2, [xvar, -i2])
        if self.verbLevel >= 2:
            self.doComment("Implicit declarations:")
            self.doComment("%d a %d %d %d 0" % (step, -xvar, i1, i2))
            self.doComment("%d a %d %d 0" % (step+1, xvar, -i1))
            self.doComment("%d a %d %d 0" % (step+2, xvar, -i2))
        self.incrStep(2)
        return step
        
    def doClause(self, lits, hints = ['*'], splitLower = False):
        if hints is None:
            hints = ['*']
        s = self.incrStep(1, splitLower)
        self.doLine([s, 'a'] + list(lits) + [0] + hints + [0], splitLower)
        self.addClause(s, lits)
        shints = None if len(hints) == 1 and hints[0] == '*' else tuple(hints)
        if s >= upperStepStart:
            self.upperHintStack.append((s,shints))
        else:
            self.lowerHintStack.append((s,shints))
        return s
        
    def doDeleteClause(self, id, hints=None):
        if hints is None:
            hints = ['*']
        self.doLine(['dc', id] + list(hints) + [0])
        self.deleteClause(id)

    def doDeleteOperation(self, exvar, clauseId, count):
        self.doLine(['do', exvar])
        for i in range(count):
            self.deleteClause(clauseId+i)
        
    def doDeleteAssertedClauses(self):
        hintStack = self.lowerHintStack + self.upperHintStack
        # final hint should be asserted unit clause.  Don't delete it
        hintStack = hintStack[:-1]
        hintStack.reverse()
        for (id,hints) in hintStack:
            self.doDeleteClause(id, hints)
            

    def finish(self):
        scount = self.lowerStepCount + (self.upperStepCount - upperStepStart)
        print("GEN: File '%s' has %d variables (%d used) and %d steps" % (self.fname, self.variableCount, len(self.usedVariableSet), scount))
        SplitWriter.finish(self)

