# Quasi-canonical representation of a POG
# For use by both top-down and bottom-up schema generators

import sys
from pysat.solvers import Solver
import readwrite

# Use glucose4 as solver
solverId = 'g4'

class PogException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Pog Exception: " + str(self.value)

# Version of reasoner that relies purely on SAT solver
class Reasoner:
    solver = None
    hintLevel = 2

    # Allow blocks of clauses, each starting with IDs at different offsets.
    # Starting with input clauses
    # Some non-input clauses can be None if want to disregard them
    clauseBlocks = [[]]
    clauseOffsets = []


    def __init__(self, inputClauseList, hintLevel):
        self.solver = Solver(solverId, with_proof = True)
        self.hintLevel = hintLevel
        clauseList = readwrite.cleanClauses(inputClauseList)
        self.clauseBlocks = [clauseList]
        self.clauseOffsets = [1]
        self.addSolverClauses(clauseList)

    def propagate(self, assumptions):
        prop, lits = self.solver.propagate(assumptions)
        return prop, lits

    def addSolverClauses(self, clist):
        self.solver.append_formula(clist)

    def rupCheck(self, clause):
        assumptions = readwrite.invertClause(clause)
        prop, slits = self.solver.propagate(assumptions)
        result = not prop
        return result

    # Add clause for future RUP derivation.  None if want to skip this one
    def addClause(self, cid, clause):
        if self.hintLevel < 4:
            return
        # See if can append this to the current clause block
        consecutiveId = len(self.clauseBlocks[-1]) + self.clauseOffsets[-1]
        if cid < consecutiveId:
            raise PogException("Can't add clause #%d.  Final clause of last block has Id %d" % (cid, consecutiveId-1))
        if cid == consecutiveId:
            self.clauseBlocks[-1].append(clause)
        else:
            # Start new block
            self.clauseBlocks.append([clause])
            self.clauseOffsets.append(cid)

    def skipClause(self, cid):
        self.addClause(cid, None)

    # See if literal among current units
    # No longer used
    def isUnit(self, lit, context):
        ok, lits = self.propagate(context)
        val = ok and lit in lits
        return val

    def justifyUnit(self, lit, context):
        clauses =  []
        if lit in context:
            return clauses
        pclause = readwrite.invertClause(context)
        pclause.append(lit)
        if self.rupCheck(pclause):
            clauses.append(pclause)
            self.addSolverClauses([pclause])
            return clauses
        # Bring out the big guns!
        sstate = self.solver.solve(assumptions=context + [-lit])
        if sstate == True:
            print("WARNING. Proof failure. Couldn't justify literal %d with context  %s" % (lit, str(context)))
            raise PogException("Proof failure. Couldn't justify literal %d with context  %s" % (lit, str(context)))
            return clauses
        slist = self.solver.get_proof()
        for sclause in slist:
            sfields = sclause.split()
            if len(sfields) > 0 and sfields[0] == 'd':
                # Ignore deletions
                continue
            try:
                fields = [int(s) for s in sfields]
            except:
                raise PogException("Proof failure.  SAT solver returned invalid proof clause %s" % sclause)
            if len(fields) == 0 or fields[-1] != 0:
                raise PogException("Proof failure.  SAT solver returned invalid proof clause %s" % sclause)
            clause = fields[:-1]
            if len(clause) ==  0:
                continue
            clauses.append(clause)
        clauses.append(pclause)
        self.addSolverClauses([pclause])
        return clauses
    
    # Find clause that is subset of target
    def findClauseId(self, tclause):
        tclause = readwrite.cleanClause(tclause)
        for (clauseList, offset) in zip(self.clauseBlocks, self.clauseOffsets):
            cid = offset            
            for clause in clauseList:
                if clause is not None and readwrite.testClauseSubset(clause, tclause):
                    return cid
                cid += 1
        return -1

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

    # Perform one pass of unit propagation through block of clauses
    # Returns pair of Booleans (found,propagated)
    # Updates search state
    def propagatePass(self, blockId, propClauses, propSet, satSet, generatorDict, unitSet):
        found = False
        propagated = False
        id = self.clauseOffsets[blockId]
        for clause in self.clauseBlocks[blockId]:
            if clause is None or id in propSet or id in satSet:
                id += 1
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
            id += 1
        return (found, propagated)

    # Try to derive RUP clause chain. Return list of hints
    # Or None if fail
    def findRup(self, tclause, inputOnly = True):
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
        blimit = 1 if inputOnly else len(self.clauseBlocks)
        found = False
        somePropagated = True

        while not found and somePropagated:
            somePropagated = False
            for bid in range(blimit):
                found, propagated = self.propagatePass(bid, propClauses, propSet, satSet, generatorDict, unitSet)
                somePropagated = somePropagated or propagated
                if found:
                    break

        # Saturation approach
#        while not found and somePropagated:
#            # Do nested iterations, where iterate through each block before moving on to next
#            somePropagated = False
#            for bid in range(blimit):
#                propagated = True
#                while not found and propagated:
#                    found, propagated = self.propagatePass(bid, propClauses, propSet, satSet, generatorDict, unitSet)
#                    somePropagated = somePropagated or propagated


        if found:
            propClauses.reverse()
            usedIdSet = set([propClauses[0]])
            hints = []
            for id in propClauses:
                if id in usedIdSet:
                    hints.append(id)
                    clause = None
                    for clauseList, offset in zip(self.clauseBlocks, self.clauseOffsets):
                        if id >= offset and id < offset+len(clauseList):
                            clause = clauseList[id-offset]
                            break
                    if clause is None:
                        continue
                    for lit in clause:
                        gen = generatorDict[abs(lit)]
                        if gen is not None:
                            usedIdSet.add(gen)
            hints.reverse()
            return hints
        else:
            return None

class NodeType:
    tcount = 5
    tautology, variable, negation, conjunction, disjunction = range(5)
    typeName = ["taut", "var", "neg", "conjunct", "disjunct"]
    definingClauseCount = [0, 0, 0, 3, 3]

# Prototype node.  Used for unique table lookup
class ProtoNode:
    ntype = None
    children =  None
    # For traversals
    mark = False 
    
    def __init__(self, ntype, children):
        self.ntype = ntype
        self.children = children
        self.mark = False

    def key(self):
        return tuple([self.ntype] + [c.xlit for c in self.children])

    def isOne(self):
        return self.ntype == NodeType.tautology

    def isZero(self):
        return self.ntype == NodeType.negation and self.children[0].isOne()

    def isConstant(self):
        return self.isOne() or self.isZero()

class Node(ProtoNode):
    xlit = None
    # Information used during proof generation.  Holdover from when node represented ITE
    iteVar = None
    dependencySet = set([])
    # Id of first clause in defining clauses
    definingClauseId = None
    # Id of clause that validates this as potential root node
    unitClauseId = None
 
    def __init__(self, xlit, ntype, children):
        ProtoNode.__init__(self, ntype, children)
        self.xlit = xlit
        self.iteVar = None
        self.dependencySet = set([])
        for child in children:
            self.dependencySet |= child.dependencySet
        self.definingClauseId = None
        self.unitClauseId = None
    
    def __hash__(self):
        return self.xlit

    def __str__(self):
        return "%s-%d" % (NodeType.typeName[self.ntype], self.xlit)

    def __eq__(self, other):
        return self.xlit == other.xlit

    def getLit(self):
        return None

class Variable(Node):

    def __init__(self, id):
        Node.__init__(self, id, NodeType.variable, [])
        self.dependencySet.add(id)

    def key(self):
        return (self.ntype, self.xlit)

    def getLit(self):
        return self.xlit

class One(Node):
    def __init__(self):
        Node.__init__(self, readwrite.tautologyId, NodeType.tautology, [])

    def __str__(self):
        return "TAUT"

class Negation(Node):
    
    def __init__(self, child):
        Node.__init__(self, -child.xlit, NodeType.negation, [child])

    def __str__(self):
        return "-" + str(self.children[0])

    def getLit(self):
        clit = self.children[0].getLit()
        return clit if clit is None else -clit

class Conjunction(Node):


    def __init__(self, children, xlit, clauseId):
        Node.__init__(self, xlit, NodeType.conjunction, children)
        self.definingClauseId = clauseId

    def __str__(self):
        return "P%d" % self.xlit

class Disjunction(Node):

    def __init__(self, child1, child2, xlit, clauseId):
        Node.__init__(self, xlit, NodeType.disjunction, [child1, child2])
        self.definingClauseId = clauseId

    def __str__(self):
        return "S%d" % self.xlit

# Represent overall POG
class Pog:
    
    # List of variables, ordered by id
    variables = []
    # Constant Nodes
    leaf1 = None
    leaf0 = None
    # Mapping (ntype, arg1, ..., argk) to nodes
    uniqueTable = {}
    # All Nodes
    nodes = []
    # Verbosity level
    verbLevel = 1
    cwriter = None
    inputClauseList = []
    reasoner = None
    # Options
    # Should unit-propagated literals be added to context?
    fullContext = True
    # Should the program attempt to fill out all hints?
    hintLevel = 2
    # Statistics:
    # Count of each node by type
    nodeCounts = []
    # Traverses of nodes by type
    nodeVisits = []
    # Added RUP clause counts, indexed by number of clauses to justify single literal
    literalClauseCounts = {}
    # Added RUP clause counts, indexed by node type
    nodeClauseCounts = []


    def __init__(self, variableCount, inputClauseList, fname, verbLevel, hintLevel):
        self.verbLevel = verbLevel
        self.hintLevel = hintLevel
        self.uniqueTable = {}
        self.inputClauseList = inputClauseList
        self.cwriter = readwrite.CratWriter(variableCount, inputClauseList, fname, verbLevel)
        self.reasoner = Reasoner(inputClauseList, hintLevel)
        self.nodeCounts = [0] * NodeType.tcount
        self.literalClauseCounts = {}
        self.nodeClauseCounts = [0] * NodeType.tcount
        self.leaf1 = One()
        self.store(self.leaf1)
        self.leaf0 = Negation(self.leaf1)
        self.store(self.leaf0)
        self.variables = []
        for i in range(1, variableCount+1):
            v = Variable(i)
            self.variables.append(v)
            self.store(v)
        # Reset so that constant nodes are not included
        self.nodeCounts = [0] * NodeType.tcount
        self.nodeVisits = [0] * NodeType.tcount
        
    def lookup(self, ntype, children):
        n = ProtoNode(ntype, children)
        key = n.key()
        if key in self.uniqueTable:
            return self.uniqueTable[key]
        return None

    def getVariable(self, id):
        return self.variables[id-1]

    def store(self, node):
        key = node.key()
        self.uniqueTable[key] = node
        self.nodes.append(node)
        self.nodeCounts[node.ntype] += 1

    def addNegation(self, child):
        if child.ntype == NodeType.negation:
            return child.children[0]
        n = self.lookup(NodeType.negation, [child])
        if n is None:
            n = Negation(child) 
            self.store(n)
        return n

    # For all nodes to be combined via conjunction
    # Returns leaf0 or list of arguments
    def mergeConjunction(self, root, sofar = []):
        if type(sofar) == type(self.leaf0) and sofar == self.leaf0:
            return sofar
        if root.isZero():
            return self.leaf0
        elif root.isOne():
            return sofar
        elif root.ntype == NodeType.conjunction:
            for child in root.children:
                sofar = self.mergeConjunction(child, sofar)
            return sofar
        else:
            sofar.append(root)
            return sofar

    def addConjunction(self, children):
        nchildren = []
        for child in children:
            nchildren = self.mergeConjunction(child, nchildren)
        if type(nchildren) == type(self.leaf0) and nchildren == self.leaf0:
            return nchildren
        children = nchildren
        n = self.lookup(NodeType.conjunction, children)
        if n is None:
            xlit, clauseId = self.cwriter.doAnd([child.xlit for child in children])
            n = Conjunction(children, xlit, clauseId)
            if self.verbLevel >= 2:
                slist = [str(child) for child in children]
                self.addComment("Node %s = AND(%s)" % (str(n), ", ".join(slist)))
            self.store(n)
        return n

    def addDisjunction(self, child1, child2, hints = None):
        if child1.isOne() or child2.isOne():
            return self.leaf1
        if child1.isZero():
            return child2
        if child2.isZero():
            return child1
        n = self.lookup(NodeType.disjunction, [child1, child2])
        if n is None:
            xlit, clauseId = self.cwriter.doOr(child1.xlit, child2.xlit, hints)
            n = Disjunction(child1, child2, xlit, clauseId)
            if self.verbLevel >= 2:
                self.addComment("Node %s = OR(%s, %s)" % (str(n), str(child1), str(child2)))
            self.store(n)
        return n

    # Find defining clauses that can be used in mutual exclusion proof
    def findHintClause(self, node, var):
        if node.ntype != NodeType.conjunction:
            return None
        for idx in range(len(node.children)):
            child = node.children[idx]
            if abs(child.xlit) == var:
                return node.definingClauseId+idx+1
        return None

    def addIte(self, nif, nthen, nelse):
        if nif.isOne():
            result = nthen
        elif nif.isZero():
            result = nelse
        elif nthen == nelse:
            result = nthen
        elif nthen.isOne() and nelse.isZero():
            result = nif
        elif nthen.isZero() and nelse.isOne():
            result = self.addNegation(nif)
        elif nthen.isOne():
            result = self.addNegation(self.addConjunction([self.addNegation(nif), self.addNegation(nelse)]))
        elif nthen.isZero():
            result = self.addConjunction(self.addNegation(nif), nelse)
        elif nelse.isOne():
            result = self.addNegation(self.addConjunction([nif, self.addNegation(nthen)]))
        elif nelse.isZero():
            result = self.addConjunction([nif, nthen])
        else:
            ntrue = self.addConjunction([nif, nthen])
            nfalse = self.addConjunction([self.addNegation(nif), nelse])
            hint1 = self.findHintClause(ntrue, nif.xlit)
            hint2 = self.findHintClause(nfalse, nif.xlit)
            if hint1 is None or hint2 is None:
                hints = None
            else:
                hints = [hint1, hint2]
            n = self.addDisjunction(ntrue, nfalse, hints)
            result = n
        if self.verbLevel >= 3:
            print("ITE(%s, %s, %s) --> %s" % (str(nif), str(nthen), str(nelse), str(result)))
        return result

    def addComment(self, s):
        self.cwriter.doComment(s)

    def deleteClause(self, id, hlist = None):
        self.cwriter.doDeleteClause(id, hlist)

    def deleteOperation(self, node):
        self.cwriter.doDeleteOperation(node.xlit, node.definingClauseId, 1+len(node.children))
        
    def validateDisjunction(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        unitClauseIds = []
        hints = []
        if root.iteVar is None:
            raise PogException("Don't know how to validate OR node %s that is not from ITE" % str(root))
        svar = root.iteVar
        # Recursively validate children
        thints, tuids = self.validateUp(root.children[0], context + [svar], root) 
        unitClauseIds += tuids
        fhints, fuids =  self.validateUp(root.children[1], context + [-svar], root)
        unitClauseIds += fuids
        # Assert extension literal.  Requires two steps to get both sides of disjunction
        if self.verbLevel >= 2:
            self.addComment("Assert ITE at node %s%s" % (str(root), rstring))
        icontext = readwrite.invertClause(context)
        clause = [-root.iteVar, root.xlit] + icontext
        if self.hintLevel >= 2:
            thints.append(root.definingClauseId+1)
            tid = self.cwriter.doClause(clause, thints)
            clause = clause[1:]
            fhints = [tid] + fhints
            fhints.append(root.definingClauseId+2)
            cid = self.cwriter.doClause(clause, fhints)
        else:
            tid = self.cwriter.doClause(clause)
            clause = clause[1:]
            cid = self.cwriter.doClause(clause)
        self.reasoner.skipClause(tid)
        self.reasoner.skipClause(cid)
        hints = [cid]
        self.nodeClauseCounts[root.ntype] += 2
        if len(context) == 0:
            root.unitClauseId = cid
            unitClauseIds.append(cid)
        return hints, unitClauseIds

    def validateConjunction(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        hints = []
        unitClauseIds = []
        vcount = 0
        ncontext = list(context)
        if self.verbLevel >= 3:
            print("Validating conjunction node %s in context %s" % (str(root), str(context)))
        for c in root.children:
            clit = c.getLit()
            if clit is None:
                chints, cuids = self.validateUp(c, ncontext, root)
                hints += chints
                unitClauseIds += cuids
                vcount += 1
                if self.verbLevel >= 3:
                    print("Got hints %s from child %s" % (str(chints), str(c)))
            else:
                if clit in ncontext:
                    if self.verbLevel >= 3:
                        print("Unit literal %d already in context %s" % (clit, str(ncontext)))
                    continue
                if self.hintLevel >= 2:
                    # See if can find subsuming input clause
                    tclause = [clit] + readwrite.invertClause(ncontext)
                    cid = self.reasoner.findClauseId(tclause)
                    if cid > 0:
                        if self.verbLevel >= 3:
                            print("Found input clause #%d=%s justifying unit literal %d in context %s.  Adding as hint" % (cid, self.inputClauseList[cid-1], clit, str(ncontext)))
                        hints.append(cid)
                        if self.fullContext:
                            ncontext.append(clit)
                        continue
                if self.hintLevel >= 3:
                    # See if can generate RUP proof over input clauses
#                    tclause = [clit] + readwrite.invertClause(ncontext)
                    rhints = self.reasoner.findRup(tclause)
                    if rhints is not None:
                        if self.verbLevel >= 3:
                            print("Justified unit literal %d in context %s with single RUP step and hints %s" % (clit, str(ncontext), str(rhints)))
                        if self.verbLevel >= 2:
                            self.addComment("Justify literal %d in context %s with single RUP step" % (clit, str(ncontext)))
                        cid = self.cwriter.doClause(tclause, rhints)
                        self.reasoner.addClause(cid, tclause)
                        # Not sure if this will ever be used
                        if len(ncontext) == 0:
                            c.unitClauseId = cid
                            unitClauseIds.append(cid)
                        hints.append(cid)
                        if self.fullContext:
                            ncontext.append(clit)
                        continue
                clauses = self.reasoner.justifyUnit(clit, ncontext)
                if len(clauses) == 0:
                    if self.verbLevel >= 3:
                        print("Found unit literal %d in context %s" % (clit, str(ncontext)))
                elif self.verbLevel >= 2:
                    self.addComment("Justify literal %d in context %s " % (clit, str(ncontext)))
                    if self.verbLevel >= 3:
                        print("Justified unit literal %d in context %s with %d proof steps" % (clit, str(ncontext), len(clauses)))
                lastCid = None
                for clause in clauses:
                    rhints = None
                    if self.hintLevel >= 4:
                        # Should be able to justify each clause
                        rhints = self.reasoner.findRup(clause, inputOnly=False)
                    if rhints is not None:
                        cid = self.cwriter.doClause(clause, rhints)
                        if self.verbLevel >= 3:
                            print("Generated hints for intermediate clause #%d" % (cid))
                    else:
                        cid = self.cwriter.doClause(clause)
                        if self.hintLevel >= 4 and self.verbLevel >= 3:
                            print("Could not generate hints for intermediate clause #%d" % (cid))
                    self.reasoner.addClause(cid, clause)
                    # This doesn't seem necessary
                    if len(ncontext) == 0 and len(clause) == 1:
                        unitClauseIds.append(cid)
                    lastCid = cid
                if lastCid is not None:
                    hints.append(lastCid)
                    if self.verbLevel >= 3:
                        print("Added hint %d" % lastCid)
                if self.fullContext:
                    ncontext.append(clit)
                nc = len(clauses)
                if nc in self.literalClauseCounts:
                    self.literalClauseCounts[nc] += 1
                else:
                    self.literalClauseCounts[nc] = 1
        if vcount > 1 or parent is None:
            # Assert extension literal
            if self.verbLevel >= 2:
                self.addComment("Assert unit clause for AND node %s%s" % (str(root), rstring))
            clause = [root.xlit] + readwrite.invertClause(context)
            hints.append(root.definingClauseId)
            if self.hintLevel >= 2:
                cid = self.cwriter.doClause(clause, hints)
            else:
                cid = self.cwriter.doClause(clause)
            self.reasoner.skipClause(cid)
            hints = [cid]
            if self.verbLevel >= 3:
                print("Asserted unit clause for AND node %s%s.  Clause #%d" % (str(root), rstring, cid))
            self.nodeClauseCounts[root.ntype] += 1
            if len(context) == 0:
                root.unitClauseId = cid
                unitClauseIds.append(cid)
        else:
            hints.append(root.definingClauseId)
            if self.verbLevel >= 3:
                print("Returned hints from AND node %s%s Hints:%s" % (str(root), rstring, str(hints)))
        return hints, unitClauseIds

    # Negated conjunction represents partial clause
    def validateNegatedConjunction(self, root, context, parent):
        nroot = root.children[0]
        rstring = " (root)" if parent is None else ""
        hints = []
        unitClauseIds = []
        # Gather children
        lits = []
        for child in nroot.children:
            lit = child.getLit()
            if lit is None:
                raise PogException("Don't know how to handle negated disjunction %s having child %s" % (str(root), str(child)))
            lits.append(lit)
        clause = [root.xlit] + readwrite.invertClause(context)
        if self.verbLevel >= 2:
            self.addComment("Assert clause for negated disjunction %s%s" % (str(root), rstring))
        if self.hintLevel >= 2:
            tclause = readwrite.invertClause(lits + context)
            cid = self.reasoner.findClauseId(tclause)
            if cid <= 0:
                raise PogException("Couldn't find input clause represented by negated disjunction %s" % (str(root)))
            hints = [nroot.definingClauseId+1+i for i in range(len(lits))] + [cid]
            cid = self.cwriter.doClause(clause, hints)
        else:
            cid = self.cwriter.doClause(clause)
        self.reasoner.skipClause(cid)
        hints = [cid]
        if len(context) == 0:
            root.unitClauseId = cid
            unitClauseIds.append(cid)
        return hints, unitClauseIds

    # Generate justification of root nodes
    # context is list of literals that are assigned in the current context
    # Returns list of unit clauses that should be deleted
    def validateUp(self, root, context, parent = None):
        self.nodeVisits[root.ntype] += 1
        if root.ntype == NodeType.disjunction:
            return self.validateDisjunction(root, context, parent)
        elif root.ntype == NodeType.conjunction:
            return self.validateConjunction(root, context, parent)
        elif root.ntype == NodeType.negation and root.children[0].ntype == NodeType.conjunction:
            return self.validateNegatedConjunction(root, context, parent)
        else:
            raise PogException("Don't know how to validate node %s" % str(root))
                

    def deletionHintsConjunction(self, root, clause):
        for idx in range(len(root.children)):
            child = root.children[idx]
            lit = child.getLit()
            if lit is None:
                vset = set([abs(lit) for lit in clause])
                if len(vset & child.dependencySet) > 0:
                    hints = self.deletionHints(child, clause)
                    hints.append(root.definingClauseId+1+idx)
                    return hints
                else:
                    continue
            else:
                if lit in clause:
                    hints = [root.definingClauseId+1+idx]
                    return hints
                else:
                    continue
        # Shouldn't get here
        raise PogException("Couldn't justify deletion of clause %s.  Reached compatible conjunction %s" % (str(clause), str(root)))

    # Want conjunction to yield true, so that its negation is false
    def deletionHintsNegatedConjunction(self, root, clause):
        for idx in range(len(root.children)):
            child = root.children[idx]
            lit = child.getLit()
            if lit is None:
                raise PogException("Couldn't justify deletion of clause %s.  Don't know how to handle negated conjunction %s" % (str(clause), str(root)))
            else:
                if -lit not in clause:
                    raise PogException("Couldn't justify deletion of clause %s.  Negated conjunction %s contains unhandled literal %d" % (str(clause), str(root), lit))
        # Checks out
        return [root.definingClauseId]

    # Generate list of hints to justify deletion of clause
    # Make sure all paths compatible with negating assignment lead to false
    # Raise error if cannot justify
    def deletionHints(self, root, clause):
        # Only need result from single visit to node
        if root.mark:
            return []
        root.mark = True
        if root.ntype == NodeType.conjunction:
            return self.deletionHintsConjunction(root, clause)
        elif root.ntype == NodeType.disjunction:
            hlist = []
            for child in root.children:
                hlist += self.deletionHints(child, clause)
            # Justify -xlit
            hlist.append(root.definingClauseId)
            return hlist
        elif root.isZero():
            return []
        elif root.isOne():
            raise PogException("Couldn't justify deletion of clause %s.  Reached terminal constant 1" % str(clause))
        elif root.ntype == NodeType.negation:
            nchild = root.children[0]
            if nchild.ntype == NodeType.conjunction:
                return self.deletionHintsNegatedConjunction(nchild, clause)
            elif child.ntype == NodeType.variable:
                lit = root.getLit()
                if lit in clause:
                    return []
                else:
                    raise PogException("Couldn't justify deletion of clause %s.  Reached terminal literal %s" % (str(clause), str(root))) 
            else:
                raise PogException("Couldn't justify deletion of clause %s.  Reached negated node with unhandled type %s" % (str(clause), str(nchild))) 
        else:
            lit = root.getLit()
            if lit is None:
                raise PogException("Couldn't justify deletion of clause %s.  Reached node with unknown type %s" % (str(clause), str(root))) 
            if lit in clause:
                return []
            else:
                raise PogException("Couldn't justify deletion of clause %s.  Reached terminal literal %s" % (str(clause), str(root))) 


    def doValidate(self):
        root = self.nodes[-1]
        hints, unitClauseIds = self.validateUp(root, [], parent = None)
        # The last one should be the root.  The others should be deleted
        topUnitId = root.unitClauseId
        unitClauseIds = unitClauseIds[:-1]
        deletedUnits = []
        # Look for special case where top-level node is conjunction
        if root.ntype == NodeType.conjunction:
            for idx in range(len(root.children)):
                child = root.children[idx]
                if child.unitClauseId is not None:
                    if self.verbLevel >= 2:
                        self.addComment("Delete extra unit clause for node %s" % str(child))
                    hints = [root.definingClauseId+1+idx, topUnitId]
                    self.deleteClause(child.unitClauseId, hints)
                    deletedUnits.append(child.unitClauseId)
        for cid in unitClauseIds:
            if cid not in deletedUnits:
                if self.verbLevel >= 2:
                    self.addComment("Delete unexpected unit clause for node %s" % str(child))
                self.deleteClause(cid)            
        if self.verbLevel >= 1:
            self.addComment("Delete input clauses")
        for cid in range(1, len(self.inputClauseList)+1):
            for node in self.nodes:
                node.mark = False
            hints = self.deletionHints(root, self.inputClauseList[cid-1])
            hints.append(topUnitId)
            self.deleteClause(cid, hints)
            
    def finish(self):
        self.cwriter.finish()
        if self.verbLevel >= 1:
            nnode = 0
            ndclause = 0
            print("c Nodes by type")
            for t in range(NodeType.tcount):
                if self.nodeCounts[t] == 0:
                    continue
                print("c    %s: %d" % (NodeType.typeName[t], self.nodeCounts[t]))
                nnode += self.nodeCounts[t]
                ndclause += NodeType.definingClauseCount[t] * self.nodeCounts[t]
            print("c    TOTAL: %d" % nnode)
            print("c Total defining clauses: %d" % ndclause)
            nvnode = 0
            print("c Node visits during proof generation (by node type)")
            for t in range(NodeType.tcount):
                if self.nodeVisits[t] == 0:
                    continue
                print("c    %s: %d" % (NodeType.typeName[t], self.nodeVisits[t]))
                nvnode += self.nodeVisits[t]
            print("c    TOTAL: %d" % nvnode)
            nlclause = 0
            print("c Literal justification clause counts (by number of clauses in justification:")
            singletons = []
            for count in sorted(self.literalClauseCounts.keys()):
                nc = self.literalClauseCounts[count]
                nlclause += count * nc
                if nc == 1:
                    singletons.append(str(count))
                else:
                    print("c    %d : %d" % (count, nc))
            print("c    1 each for counts %s" % ", ".join(singletons))
            print("c    TOTAL: %d" % nlclause)
            nnclause = 0
            print("c RUP clauses for node justification (by node type):")
            for t in range(NodeType.tcount):
                if self.nodeClauseCounts[t] == 0:
                    continue
                print("c    %s: %d" % (NodeType.typeName[t], self.nodeClauseCounts[t]))
                nnclause += self.nodeClauseCounts[t]
            print("c    TOTAL: %d" % nnclause)
            niclause = len(self.inputClauseList)
            nclause = niclause + ndclause + nlclause + nnclause
            print("Total clauses: %d input + %d defining + %d literal justification + %d node justifications = %d" % (niclause, ndclause, nlclause, nnclause, nclause))

    def doMark(self, root, markSet):
        if root.xlit in markSet:
            return
        markSet.add(root.xlit)
        for c in root.children:
            self.doMark(c, markSet)
        
    # Perform mark & sweep to remove any nodes not reachable from root
    def compress(self):
        markSet = set([])
        root = self.nodes[-1]
        self.doMark(root, markSet)
        nnodes = []
        for node in self.nodes:
            if node.xlit in markSet:
                nnodes.append(node)
        if self.verbLevel >= 2:
            print("Compressed POG from %d to %d nodes" % (len(self.nodes), len(nnodes)))
        self.nodes = nnodes


    def show(self):
        for node in self.nodes:
            if node.ntype != NodeType.negation:
                outs = str(node)
                schildren = [str(c) for c in node.children]
                if len(schildren) > 0:
                    outs += " (" + ", ".join(schildren) + ")"
                print(outs)
        print("Root = %s" % str(self.nodes[-1]))
            
        
        
