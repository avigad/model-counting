#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
# Last edit: June 19, 2022
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


# Checker for CRAT POG.
import sys
import getopt
import datetime

def usage(name):
    print("Usage: %s [-v] [-L] -i FILE.cnf -p FILE.crat [-w W1:W2:...:Wn] [-o FILE.crat]" % name)
    print("   -v VLEVEL    Set verbosity level (0-3)")
    print("   -L           Lax mode: Don't attempt validation of *'ed hints")
    print("   -w WEIGHTS   Provide colon-separated set of input weights.")
    print("                Each should be between 0 and 100 (will be scaled by 1/100)")
    print("   -o FILE.crat Produce CRAT output file with all hints present")


######################################################################################
# CRAT Syntax
######################################################################################
# Notation
#  Id: Clause Id
#  Var: Variable
#  Lit: Literal +/- Var

# Lit*: Clause consisting of specified literals
# HINT: Either Id+ or *

# Id  i [Lit*] 0             -- Input clause
# Id  a [Lit*] 0    HINT 0   -- RUP clause addition
#    dc Id          HINT 0   -- RUP clause deletion
# Id  p Var Lit Lit+     0   -- And operation
# Id  a Var Lit Lit HINT 0   -- Or operation
#    do Var                  -- Operation deletion

######################################################################################

def trim(s):
    while len(s) > 0 and s[-1] in ' \r\n\t':
        s = s[:-1]
    return s


# Clean up clause.
# Remove duplicates
# Sort in reverse order of variable number
# Don't allow clause to have opposite literals
def cleanClause(literalList):
    slist = sorted(literalList, key = lambda v: -abs(v))
    if len(slist) <= 1:
        return slist
    nlist = [slist[0]]
    for i in range(1, len(slist)):
        if slist[i-1] == slist[i]:
            continue
        if slist[i-1] == -slist[i]:
            return None
        nlist.append(slist[i])
    return nlist

def regularClause(clause):
    return clause is not None

def showClause(clause):
    if clause is None:
        return "NONE"
    return str(clause)

class RupException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "RUP Exception: " + str(self.value)


# Clause comparison.  Assumes both have been processed by cleanClause
def testClauseEquality(clause1, clause2):
    if clause1 is None or clause2 is None:
        return False
    if len(clause1) != len(clause2):
        return False
    for l1, l2 in zip(clause1, clause2):
        if l1 != l2:
            return False
    return True

class PNumException(Exception):
    msg = ""

    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "P52 Number exception %s" % self.msg



# Represent numbers of form a * 2**m2 + 5**m5
class P52:
    a = 1
    m2 = 0
    m5 = 0

    def __init__(self, a=0, m2=0, m5=0):
        if type(a) != type(1):
            raise PNumException("Nonintegral a (%s)" % str(a))
        if type(m2) != type(1):
            raise PNumException("Nonintegral m2 (%s)" % str(m2))
        if type(m5) != type(1):
            raise PNumException("Nonintegral m5 (%s)" % str(m5))
        if a == 0:
            self.a = a
            self.m2 = 0
            self.m5 = 0
            return
        while a % 2 == 0:
            a = a//2
            m2 += 1
        while a % 5 == 0:
            a = a//5
            m5 += 1
        self.a = a
        self.m2 = m2
        self.m5 = m5

    def __str__(self):
        return "%d*2^(%d)5^(%d)" % (self.a, self.m2, self.m5)

    def num(self):
        p2 = 2**self.m2
        p5 = 5**self.m5
        val = self.a * p2 * p5
        return val


    def neg(self):
        result = P52(-self.a, self.m2, self.m5)
        return result

    def oneminus(self):
        one = P52(1)
        result = one.add(self.neg())
        return result

    def mul(self, other):
        na = self.a * other.a 
        nm2 = self.m2 + other.m2
        nm5 = self.m5 + other.m5
        result =  P52(na, nm2, nm5)
        return result

    def add(self, other):
        ax = self.a
        ay = other.a
        m2x = self.m2
        m2y = other.m2
        m5x = self.m5
        m5y = other.m5
        if m2y > m2x:
            d2 = m2y-m2x
            ay *= 2**d2
            m2n = m2x
        else:
            d2 = m2x-m2y
            ax *= 2**d2
            m2n = m2y
        if m5y > m5x:
            d5 = m5y-m5x
            ay *= 5**d5
            m5n = m5x
        else:
            d5 = m5x-m5y
            ax *= 5**d5
            m5n = m5y
        an = ax+ay
        result = P52(an, m2n, m5n)
        return result

    def scale2(self, x):
        return P52(self.a, self.m2+x, self.m5)
    def scale5(self, x):
        return P52(self.a, self.m2, self.m5+x)
    def scale10(self, x):
        return P52(self.a, self.m2+x, self.m5+x)

    def parse(self, s):
        if len(s) == 0:
            raise PNumException("Invalid number '%s'" % s)
        negative = s[0] == '-'
        if negative:
            s = s[1:]
        fields = s.split('.')
        if len(fields) == 1:
            try:
                ival = int(fields[0])
                if negative:
                    ival = -ival
            except:
                raise PNumException("Invalid number '%s'" % s)
            return P52(ival)
        elif len(fields) == 2:
            try:
                h = int(fields[0]) if len(fields[0]) > 0 else 0
                l = int(fields[1]) if len(fields[1]) > 0 else 0
                if negative:
                    h = -h
                    l = -l
            except:
                raise PNumException("Invalid number '%s'" % s)
            wt = len(fields[1])
            return P52(h).add(P52(l,-wt,-wt))
        else:
            raise PNumException("Invalid number '%s'" % s)

    def render(self):
        if self.a < 0:
            sign = "-"
            ival = -self.a
        else:
            sign = ""
            ival = self.a
        p10 = min(self.m2, self.m5)
        if self.m2 > p10:
            ival *= 2**(self.m2 - p10)
        elif self.m5 > p10:
            ival *= 5**(self.m5 - p10)
        sval = str(ival)
        if p10 >= 0:
            sval += '0' * p10
        elif -p10 >= len(sval):
            sval = '0.' + '0' * -(p10+len(sval)) + sval
        else:
            pos = len(sval) + p10
            sval = sval[:pos] + '.' + sval[pos:]
        return sign+sval

    
# Read CNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
class CnfReader():
    file = None
    clauses = []
    # List of input variables.
    nvar = 0
    failed = False
    errorMessage = ""
    
    def __init__(self, fname):
        self.failed = False
        self.errorMessage = ""
        try:
            self.file = open(fname, 'r')
        except Exception:
            self.fail("Could not open file '%s'" % fname)
            return
        self.readCnf()
        print("Read %d clauses from file %s" % (len(self.clauses), fname))
        self.file.close()
        
    def fail(self, msg):
        self.failed = True
        self.errorMessage = msg

    def readCnf(self):
        self.nvar = 0
        lineNumber = 0
        nclause = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
                pass
            elif line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    self.fail("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                    return
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    self.fail("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
                    return
            else:
                if nclause == 0:
                    self.fail("Line %d.  No header line.  Not cnf" % (lineNumber))
                    return
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    self.fail("Line %d.  Non-integer field" % lineNumber)
                    return
                # Last one should be 0
                if lits[-1] != 0:
                    self.fail("Line %d.  Clause line should end with 0" % lineNumber)
                    return
                lits = lits[:-1]
                vars = sorted([abs(l) for l in lits])
                if len(vars) == 0:
                    self.fail("Line %d.  Empty clause" % lineNumber)                    
                    return
                if vars[-1] > self.nvar or vars[0] == 0:
                    self.fail("Line %d.  Out-of-range literal" % lineNumber)
                    return
                for i in range(len(vars) - 1):
                    if vars[i] == vars[i+1]:
                        self.fail("Line %d.  Opposite or repeated literal" % lineNumber)
                        return
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            self.fail("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
            return

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

class CratWriter(Writer):
    variableCount = 0
    clauseDict = []
    stepCount = 0

    def __init__(self, variableCount, clauseList, fname, verbLevel = 1):
        Writer.__init__(self, variableCount, fname, verbLevel=verbLevel, isNull=False)
        self.variableCount = variableCount
        self.stepCount = len(clauseList)
        self.clauseDict = {}
        if verbLevel >= 2 and len(clauseList) > 0:
            self.doComment("Input clauses")
        for s in range(1, len(clauseList)+1):
            lits = clauseList[s-1]
            if verbLevel >= 2:
                self.doLine([s, 'i'] + lits + [0])
            self.addClause(s, lits)

    def addClause(self, step, lits):
        self.clauseDict[step] = lits

    def deleteClause(self, step):
        del self.clauseDict[step]

    def doLine(self, items):
        slist = [str(i) for i in items]
        self.show(" ".join(slist))

    def doComment(self, line):
        self.show("c " + line)
        
    def doAnd(self, args, xvar = None, id = None):
        self.variableCount += 1
        self.stepCount += 1
        v = self.variableCount if xvar is None else xvar
        s = self.stepCount if id is None else id

        self.doLine([s, 'p', v] + args + [0])
        cpos = [v] + [-i for i in args]
        self.addClause(s, cpos)
        if self.verbLevel >= 2:
            self.doComment("Implicit declarations:")
            slist = [str(lit) for lit in cpos]
            self.doComment("%d a %s 0" % (s, " ".join(slist)))
        for idx in range(len(args)):
            self.addClause(s+idx, [-v, args[idx]])
            if self.verbLevel >= 2:
                self.doComment("%d a %d %d 0" % (s+1+idx, -v, args[idx]))
        self.stepCount += len(args)
        return (v, s)

    def doOr(self, i1, i2, hints = None, xvar = None, id = None):
        if hints is None:
            hints = ['*']
        self.variableCount += 1
        self.stepCount += 1
        v = self.variableCount if xvar is None else xvar
        s = self.stepCount if id is None else id
        self.doLine([s, 's', v, i1, i2] + hints + [0])
        self.addClause(s, [-v, i1, i2])
        self.addClause(s+1, [v, -i1])        
        self.addClause(s+2, [v, -i2])
        if self.verbLevel >= 2:
            self.doComment("Implicit declarations:")
            self.doComment("%d a %d %d %d 0" % (s, -v, i1, i2))
            self.doComment("%d a %d %d 0" % (s+1, v, -i1))
            self.doComment("%d a %d %d 0" % (s+2, v, -i2))
        self.stepCount += 2
        return (v, s)
        
    def doClause(self, lits, hints = ['*'], id = None):
        self.stepCount += 1
        s = self.stepCount if id is None else id
        self.doLine([s, 'a'] + lits + [0] + hints + [0])
        self.addClause(s, lits)
        return s
        
    def doDeleteClause(self, id, hints=None):
        if hints is None:
            hints = ['*']
        self.doLine(['dc', id] + hints + [0])
        self.deleteClause(id)

    def doDeleteOperation(self, exvar, clauseId):
        self.doLine(['do', exvar])
        for i in range(3):
            self.deleteClause(clauseId+i)
        
        
    def finish(self):
        print("c File '%s' has %d variables and %d steps" % (self.fname, self.variableCount, self.stepCount))
        Writer.finish(self)


# Clause processing
class ClauseManager:
    # Number of input clauses
    inputClauseCount = 0
    # Mapping from Id to clause.  Deleted clauses represented by None
    clauseDict = {}
    # Unit clauses
    unitClauseSet = set([])
    # For each literal, count of clauses containing it
    literalCountDict = {}
    # For each literal, set of clauses containing it (only in verbose mode)
    literalSetDict = {}
    # Track whether have empty clause
    addedEmpty = False
    # Counters
    liveClauseCount = 0
    maxLiveClauseCount = 0
    totalClauseCount = 0
    # Maximum clause ID.  Used to ensure ascending order
    maxClauseId = 0
    # Clauses that haven't been deleted (only in verbose mode)
    liveClauseSet = set([])
    # Final root 
    root = None
    verbose = False
    laxMode = False
    uncheckedCount = 0

    def __init__(self, clauseCount, verbose, laxMode):
        self.inputClauseCount = clauseCount
        self.verbose = verbose
        self.laxMode = laxMode
        self.uncheckedCount = 0
        self.clauseDict = {}
        self.unitClauseSet = set([])
        self.literalCountDict = {}
        self.literalSetDict = {}
        self.addedEmpty = False
        self.liveClauseCount = 0
        self.maxLiveClauseCount = 0
        self.totalClauseCount = 0
        self.liveClauseSet = set([])
        self.root = None

    def findClause(self, id):
        if id not in self.clauseDict:
            return (None, "Clause #%d never defined" % id)
        elif self.clauseDict[id] is None:
            return (None, "Clause #%d has been deleted" % id)
        else:
            return (self.clauseDict[id], "")

    # Add clause.  Should have been processed with cleanClause
    # Return (T/F, reason)
    def addClause(self, clause, id):
        if not regularClause(clause):
            return (False, "Cannot add clause %s" % showClause(clause))
        if id <= self.maxClauseId:
            return (False, "Invalid clause Id %d.  Not in ascending order" % (id))
        self.maxClauseId = id
        self.clauseDict[id] = clause
        if len(clause) == 0:
            self.addedEmpty = True
        if len(clause) == 1:
            self.unitClauseSet.add(id)
        self.liveClauseCount += 1
        self.totalClauseCount += 1
        if self.verbose:
            self.liveClauseSet.add(id)
        self.maxLiveClauseCount = max(self.liveClauseCount, self.maxLiveClauseCount)
        # Add literals
        for lit in clause:
            if lit in self.literalCountDict:
                self.literalCountDict[lit] += 1
                if self.verbose:
                    self.literalSetDict[lit].add(id)
            else:
                self.literalCountDict[lit] = 1
                if self.verbose:
                    self.literalSetDict[lit] = set([id])
        return (True, "")
        
    # Delete clause.
    # Return (T/F, reason)
    def deleteClause(self, id):
        clause, msg = self.findClause(id)
        if clause is None:
            return (False, "Cannot delete clause %d: %s" % (id, msg))
        self.clauseDict[id] = None
        if id in self.unitClauseSet:
            self.unitClauseSet.remove(id)
        self.liveClauseCount -= 1
        if self.verbose:
            self.liveClauseSet.remove(id)
        for lit in clause:
            self.literalCountDict[lit] -= 1
            if self.verbose:
                self.literalSetDict[lit].remove(id)
        return (True, "")
        
    # Unit propagation.  Given clause and set of satisfied literals.
    # Return: ("unit", ulit), ("conflict", None), ("satisfied", lit), ("none", None)
    def unitProp(self, clause, unitSet):
        ulit = None
        for lit in clause:
            if lit in unitSet:
                return ("satisfied", lit)
            if -lit not in unitSet:
                if ulit is None:
                    ulit = lit
                else:
                    # No unit literal found
                    return ("none", None)
        if ulit is None:
            return ("conflict", None)
        unitSet.add(ulit)
        return ("unit", ulit)

    # Try to derive RUP clause chain. Return list of hints
    def findRup(self, tclause):
        # List of clause Ids that have been used in unit propagation
        propClauses = []
        # Set of clause Ids that have been used in unit propagation
        propSet = set([])
        # Set of clause Ids that are satisfied during unit propagation
        satSet = set([])
        # For each variable unit literal, either id of generating clause or None when comes from target
        generatorDict = {}
        # Set of unit literals
        unitSet = set([])
        for lit in tclause:
            unitSet.add(-lit)
            generatorDict[abs(lit)] = None
        found = False
        propagated = True
        while propagated and not found:
            propagated = False
            for id in self.clauseDict.keys():
                if id not in propSet and id not in satSet:
                    clause, msg = self.findClause(id)
                    if clause is None:
                        continue
                    (uresult, ulit) = self.unitProp(clause, unitSet)
                    if uresult == "satisfied":
                        satSet.add(id)
                    elif uresult == "unit":
                        propagated = True
                        propClauses.append(id)
                        propSet.add(id)
                        generatorDict[abs(ulit)] = id
                    elif uresult == "conflict":
                        propClauses.append(id)
                        found = True
                        break
        if found:
            propClauses.reverse()
            usedIdSet = set([propClauses[0]])
            hints = []
            for id in propClauses:
                if id in usedIdSet:
                    hints.append(id)
                    clause, msg = self.findClause(id)
                    if clause is None:
                        continue
                    for lit in clause:
                        gen = generatorDict[abs(lit)]
                        if gen is not None:
                            usedIdSet.add(gen)
            hints.reverse()
            if self.verbose:
                print("RUP finder: Target = %s.  Hints = %s" % (str(tclause), str(hints)))
            return hints
        else:
            if self.verbose:
                print("RUP finder failed: Target = %s.  Units = %s" % (str(tclause), str(list(unitSet))))
            return None

    # Check that clause is generated by set of antecedents
    # Assumes clause has been processed by cleanClause
    # Return (T/F, Reason, hints)
    def checkRup(self, clause, hints):
        if len(hints) == 1 and hints[0] == '*':
            if self.laxMode:
                self.uncheckedCount += 1
                return (True, "")
            hints = self.findRup(clause)
            if hints is None:
                return (False, "RUP failed for clause %s: Couldn't generate hints" % (showClause(clause)), hints)
        unitSet = set([-lit for lit in clause])
        for id in hints:
            rclause, msg = self.findClause(id)
            if rclause is None:
                return (False, "RUP failed: %s" % msg, hints)
            uresult, ulit = self.unitProp(rclause, unitSet)
            if uresult == "none":
                return (False, "RUP failed for clause %s: No unit literal found in clause #%d %s" % (showClause(clause) ,id, showClause(rclause)), hints)
            elif uresult == "satisfied":
                return (False, "RUP failed for clause %s: Literal %s true in clause #%d %s" % (showClause(clause), ulit, id, showClause(rclause)), hints)
            elif uresult == "conflict":
                return (True, "", hints)
        return (False, "RUP failed: No conflict found", hints)

    def checkFinal(self):
        # All input clauses should have been deleted
        neverDefined = []
        notDeleted = []
        for id in range(1, self.inputClauseCount+1):
            if id in self.clauseDict:
                if self.clauseDict[id] is not None:
                    notDeleted.append(id)
            else:
                neverDefined.append(id)
        if len(neverDefined) > 0:
            return (False, "Input clauses %s never defined" % str(neverDefined))
        if len(notDeleted) > 0:
            return (False, "Input clauses %s not deleted" % str(notDeleted))
        # Should only be one unit clause
        self.root = None
        for id in sorted(self.clauseDict.keys()):
            entry = self.clauseDict[id]
            if entry is None:
                continue
            if len(entry) == 1:
                nroot = entry[0]
                if self.root is not None:
                    return (False, "At least two possible roots: %d, %d" % (self.root, nroot))
                self.root = nroot
        if self.root is None:
            return (False, "No root found")
        return (True, "")

class OperationManager:
    conjunction, disjunction = range(2)
    
    # Number of input variables
    inputVariableCount = 0
    # Operation indexed by output variable.  Each entry of form (id, op, arg1, arg2, ...)
    operationDict = {}
    # For each variable, the variables on which it depends
    dependencySetDict = {}

    # Clause Manager
    cmgr = None
    verbose = False

    def __init__(self, cmgr, varCount):
        self.inputVariableCount = varCount
        self.cmgr = cmgr
        self.verbose = cmgr.verbose
        self.operationDict = {}
        self.dependencySetDict = { v : set([v]) for v in range(1, varCount+1) }

    def addOperation(self, op, outVar, inLits, id):
        if op == self.disjunction:
            if len(inLits) != 2:
                return (False, "Cannot have %d arguments for disjunction" % len(inLits))
        elif op == self.conjunction:
            if len(inLits) < 2:
                return (False, "Cannot have %d arguments for conjunction" % len(inLits))
        if outVar in self.dependencySetDict:
            return (False, "Operator output variable %d already in use" % outVar)
        dset = set([])
        for lit in inLits:
            var = abs(lit)
            if var not in self.dependencySetDict:
                return (False, "Operator input literal %d undefined" % lit)
            adset = self.dependencySetDict[var]
            if op == self.conjunction and not adset.isdisjoint(dset):
                return (False, "Overlapping dependency sets for conjunction operation")
            dset = dset.union(adset)
        self.dependencySetDict[outVar] = dset
        if op == self.conjunction:
            (ok, msg) = self.cmgr.addClause([outVar] + [-lit for lit in inLits], id)
            if not ok:
                return (ok, msg)
            nextId = id+1
            for lit in inLits:
                (ok, msg) = self.cmgr.addClause([-outVar, lit], nextId)
                nextId += 1
                if not ok:
                    return (ok, msg)
        elif op == self.disjunction:
            (ok, msg) = self.cmgr.addClause([-outVar] + inLits, id)
            if not ok:
                return (ok, msg)
            nextId = id+1
            for lit in inLits:
                (ok, msg) = self.cmgr.addClause([outVar, -lit], nextId)
                nextId += 1
                if not ok:
                    return (ok, msg)
            if not ok:
                return (ok, msg)
        self.operationDict[outVar] = tuple([id, op] + inLits)
        return (True, "")

    def checkDisjunction(self, inLit1, inLit2, hints):
        return self.cmgr.checkRup([-inLit1, -inLit2], hints)

    def deleteOperation(self, outVar):
        if outVar not in self.operationDict:
            return (False, "Operator %d undefined" % outVar)
        entry = self.operationDict[outVar]
        id = entry[0]
        op = entry[1]
        args = entry[2:]
        for i in range(len(args)+1):
            (ok, msg) = self.cmgr.deleteClause(id+i)
            if not ok:
                return (False, "Could not delete defining clause #%d for operation %d: %s" % (id+i, outVar, msg))
        lcount = self.cmgr.literalCountDict[outVar] + self.cmgr.literalCountDict[-outVar]
        if lcount > 0:
            if self.verbose:
                clist = list(self.cmgr.literalSetDict[outVar]) + list(self.cmgr.literalSetDict[-outVar])
                return (False, "Could not delete operation %d: Clauses %s still reference it." % (outVar, str(clist)))
            else:
                return (False, "Could not delete operation %d: %d clauses still reference it." % (outVar, lcount))

        del self.operationDict[outVar]
        del self.dependencySetDict[outVar]
        return (True, "")

    def pnumCount(self, root, weights, finalScale = None):
        for outVar in sorted(self.operationDict.keys()):
            entry = self.operationDict[outVar]
            id = entry[0]
            op = entry[1]
            args = entry[2:]
            wts = []
            for arg in args:
                var = abs(arg)
                val = weights[var]
                if arg < 0:
                    val = val.oneminus()
                wts.append(val)
            result = wts[0]
            for w in wts[1:]:
                result = result.mul(w) if op == self.conjunction else result.add(w)
            weights[outVar] = result
        rootVar = abs(root)
        rval = weights[rootVar]
        if root < 0:
            rval = rval.oneminus()
        if finalScale is not None:
            rval = rval.mul(finalScale)
        return rval
    

    # Optionally provide dictionary of weights.  Otherwise assume unweighted
    def count(self, root, weights = None, finalScale = None):
        if weights is None:
            weights = { v : P52(1,-1,0) for v in range(1, self.inputVariableCount+1) }
            finalScale = P52(1, self.inputVariableCount, 0)
        pval = self.pnumCount(root, weights, finalScale)
        return pval

class ProofException(Exception):
    def __init__(self, value, lineNumber = None):
        self.value = value
        self.lineNumber = lineNumber

    def __str__(self):
        nstring = " (Line %d)" % self.lineNumber if self.lineNumber is not None else ""
        return ("Proof Exception%s: " % nstring) + str(self.value)

class Prover:
    verbose = False
    lineNumber = 0
    # Clause Manager
    cmgr = None
    # Operation Manager
    omgr = None
    failed = False
    # Make copy of CRAT file with hints
    cratWriter = None


    def __init__(self, creader, verbose = False, laxMode = False, cratWriter=None):
        self.verbose = verbose
        self.lineNumber = 0
        self.cmgr = ClauseManager(len(creader.clauses), verbose, laxMode)
        self.omgr = OperationManager(self.cmgr, creader.nvar)
        self.cratWriter = cratWriter
        self.failed = False
        self.subsetOK = False
        self.ruleCounters = { 'i' : 0, 'a' : 0, 'dc' : 0, 'p' : 0, 's' : 0, 'do' : 0 }

        id = 0
        for clause in creader.clauses:
            nclause = cleanClause(clause)
            if not regularClause(nclause):
                self.failProof("Cannot add %s as input clause" % showClause(clause))
                break
            id += 1
            (ok, msg) = self.cmgr.addClause(nclause, id)
            if not ok:
                self.failProof(msg)
                break

    def flagError(self, msg):
        print("ERROR.  Line %d: %s" % (self.lineNumber, msg))
        self.failed = True

    # Find zero-terminated list of integers in fields (or single field consisting of '*').  Return (list, rest)
    # Flag error if something goes wrong
    def findList(self, fields, starOk = False):
        ls = []
        rest = fields
        starOk = True
        while len(rest) > 0:
            field = rest[0]
            rest = rest[1:]
            if starOk and field == '*':
                val = '*'
            else:
                try:
                    val = int(field)
                except:
                    self.flagError("Non-integer value '%s' encountered" % field)
                    return (ls, rest)
            if val == 0:
                return (ls, rest)
            ls.append(val)
            starOk = False
        self.flagError("No terminating 0 found")
        return (ls, rest)

    def prove(self, fname):
        if self.failed:
            self.failProof("Problem with CNF file")
            return
        try:
            pfile = open(fname)
        except:
            self.failProof("Couldn't open proof file '%s" % fname)
            return
        for line in pfile:
            self.lineNumber += 1
            fields = line.split()
            if len(fields) == 0 or fields[0][0] == 'c':
                continue
            id = None
            if fields[0] not in ['dc', 'do']:
                try:
                    id = int(fields[0])
                except:
                    self.flagError("Looking for clause Id.  Got '%s'" % fields[0])
                    break
                fields = fields[1:]
            cmd = fields[0]
            rest = fields[1:]
            # Dispatch on command
            # Level command requires special consideration, since it only occurs at beginning of file
            if cmd == 'i':
                self.doInput(id, rest)
            elif cmd == 'a':
                self.doAddRup(id, rest)
            elif cmd == 'dc':
                self.doDeleteRup(id, rest)
            elif cmd == 'p':
                self.doProduct(id, rest)
            elif cmd == 's':
                self.doSum(id, rest)
            elif cmd == 'do':
                self.doDeleteOperation(id, rest)
            else:
                self.invalidCommand(cmd)
            if self.failed:
                break
            self.ruleCounters[cmd] += 1
        if not self.failed:
            (ok, msg) = self.cmgr.checkFinal()
            if not ok:
                self.flagError(msg)
        pfile.close()
        self.checkProof()
            
    def count(self, weights = None):
        root = self.cmgr.root
        if root is None:
            print("Can't determine count.  Don't know root")
            return 0.0
        return self.omgr.count(self.cmgr.root, weights)

    def invalidCommand(self, cmd):
        self.flagError("Invalid command '%s' in proof" % cmd)

    def doInput(self, id, rest):
        (lits, rest) = self.findList(rest)
        if self.failed:
            return
        if len(rest) > 0:
            self.flagError("Items beyond terminating 0")
        clause = cleanClause(lits)
        if not testClauseEquality(clause, self.cmgr.clauseDict[id]):
            self.flagError("Clause %s does not match input clause #%d" % (showClause(lits), id))
            return

    def doAddRup(self, id, rest):
        (lits, rest) = self.findList(rest)
        if self.failed:
            return
        (hints, rest) = self.findList(rest, starOk = True)
        if self.failed:
            return
        if len(rest) > 0:
            self.flagError("Coudn't add clause #%d: Items beyond terminating 0" % (id))
            return
        if self.verbose:
            print("AddRup step #%d.  Lits = %s" % (id, str(lits)))
        clause = cleanClause(lits)
        (ok, msg, hints) = self.cmgr.checkRup(clause, hints)
        if not ok:
            self.flagError("Couldn't add clause #%d: %s" % (id, msg))
            return
        (ok, msg) = self.cmgr.addClause(clause, id)
        if not ok:
            self.flagError("Couldn't add clause #%d: %s" % (id, msg))
        if self.cratWriter is not None:
            self.cratWriter.doClause(lits, hints, id = id)

    def doDeleteRup(self, id, rest):
        if len(rest) < 1:
            self.flagError("Must specify Id of clause to delete")
            return
        try:
            id = int(rest[0])
        except:
            self.flagError("Couldn't delete clause.  Invalid clause Id '%s'" % rest[0])
            return
        rest = rest[1:]
        (hints, rest) = self.findList(rest, starOk = True)
        if self.failed:
            return
        if len(rest) > 0:
            self.flagError("Couldn't delete clause #%d: Items beyond terminating 0" % (id))
            return
        (clause, msg) = self.cmgr.findClause(id)
        if clause is None:
            self.flagError("Couldn't delete clause #%d: %s" % (id, msg))
            return
        (ok, msg) = self.cmgr.deleteClause(id)
        if not ok:
            self.flagError("Couldn't delete clause #%d: %s" % (id, msg))
            return
        (ok, msg, hints) = self.cmgr.checkRup(clause, hints)
        if not ok:
            self.flagError("Couldn't delete clause #%d: %s" % (id, msg))
            return
        if self.cratWriter is not None:
            self.cratWriter.doDeleteClause(id, hints)
        
    def doProduct(self, id, rest):
        if len(rest) < 4:
            self.flagError("Couldn't add product operation with clause #%d: Invalid number of operands" % (id))
            return
        try:
            args = [int(field) for field in rest]
        except:
            self.flagError("Couldn't add operation with clause #%d: Non-integer arguments" % (id))
            return
        if args[-1] != 0:
            self.flagError("Couldn't add operation with clause #%d: No terminating 0 found" % (id))
            return
        args = args[:-1]
        (ok, msg) = self.omgr.addOperation(self.omgr.conjunction, args[0], args[1:], id)
        if not ok:
            self.flagError("Couldn't add operation with clause #%d: %s" % (id, msg))
        if self.cratWriter is not None:
            self.cratWriter.doAnd(args[1:], xvar=args[0], id=id)

    def doSum(self, id, rest):
        if len(rest) < 3:
            self.flagError("Couldn't add sum operation with clause #%d: Invalid number of operands" % (id))
            return
        try:
            args = [int(field) for field in rest[:3]]
            rest = rest[3:]
        except:
            self.flagError("Couldn't add operation with clause #%d: Non-integer arguments" % (id))
            return
        (hints, rest) = self.findList(rest, starOk = True)
        if self.failed:
            return
        (ok, msg) = self.omgr.addOperation(self.omgr.disjunction, args[0], [args[1], args[2]], id)
        if not ok:
            self.flagError("Couldn't add operation with clause #%d: %s" % (id, msg))
            return
        if len(rest) > 0:
            self.flagError("Couldn't add operation with clause #%d: Items beyond terminating 0" % (id))
            return
        (ok, msg, hints) = self.omgr.checkDisjunction(args[1], args[2], hints)
        if not ok:
            self.flagError("Couldn't add operation with clause #%d: %s" % (id, msg))
            return
        if self.cratWriter is not None:
            self.cratWriter.doOr(args[1], args[2], hints = hints, xvar=args[0], id=id)

    def doDeleteOperation(self, id, rest):
        if len(rest) != 1:
            self.flagError("Must specify output variable for operation deletion")
            return
        try:
            outVar = int(rest[0])
        except:
            self.flagError("Invalid operand '%s' to operation deletion" % rest[0])
            return
        (ok, msg) = self.omgr.deleteOperation(outVar)
        if not ok:
            self.flagError("Could not delete operation %d: %s" % (outVar, msg))

    def failProof(self, reason):
        self.failed = True
        msg = "PROOF FAILED"
        if reason != "":
            msg += ": " + reason
        print(msg)

    def checkProof(self):
        if self.failed:
            self.failProof("")
        else:
            if self.cmgr.uncheckedCount == 0:
                print("PROOF SUCCESSFUL")
            else:
                print("PROOF UNVERIFIED (%d unchecked hints)" % self.cmgr.uncheckedCount)
        self.summarize()
            
    def summarize(self):
        clist = sorted(self.ruleCounters.keys())
        tcount = 0
        print("%d total clauses" % self.cmgr.totalClauseCount)
        print("%d maximum live clauses" % self.cmgr.maxLiveClauseCount)
        print("Command occurences:")
        for cmd in clist:
            count = self.ruleCounters[cmd]
            if count > 0:
                tcount += count
                print("    %2s   : %d" % (cmd, count))
        print("    TOTAL: %d" % (tcount))


def run(name, args):
    cnfName = None
    proofName = None
    cratName = None
    verbLevel = 1
    laxMode = False
    weights = None
    optList, args = getopt.getopt(args, "hv:Li:p:w:o:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-L':
            laxMode = True
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            proofName = val
        elif opt == '-o':
            cratName = val
        elif opt == '-w':
            wlist = val.split(":")
            try:
                weights = { v : P52(int(wlist[v-1]), -2, -2) for v in range(1, len(wlist)+1) }
            except Exception as ex:
                print("Couldn't extract weights from '%s' (%s)" % (val, str(ex)))
                usage(name)
                return
        else:
            usage(name)
            return
    if cnfName is None:
        print("Need CNF file name")
        return
    if proofName is None:
        print("Need proof file name")
        return
    start = datetime.datetime.now()
    creader = CnfReader(cnfName)
    if creader.failed:
        print("Error reading CNF file: %s" % creader.errorMessage)
        print("PROOF FAILED")
        return
    if weights is not None and len(weights) != creader.nvar:
        print("Invalid set of weights.  Should provide %d.  Got %d" % (creader.nvar, len(weights)))
        return
    verbose = verbLevel > 1
    cratWriter = None
    if cratName is not None:
        cratWriter = CratWriter(creader.nvar, creader.clauses, cratName, verbLevel)
    prover = Prover(creader, verbose, laxMode, cratWriter)
    prover.prove(proofName)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    print("Elapsed time for check: %.2f seconds" % seconds)
    count = prover.count(weights)
    if weights is None:
        print("Unweighted count = %s" % count.render())
    else:
        print("Weighted count = %s" % count.render())
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
