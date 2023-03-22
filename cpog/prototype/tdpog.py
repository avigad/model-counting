# Quasi-canonical representation of a POG
# For use by top-down POG generators

import sys
from pysat.solvers import Solver
import readwrite

# Global options
# Should input clauses be stored in dictionary?
mapInputClauseSetting = True
# What categories of clauses should be checked?
maxCategorySetting = 0
# Should conjunctions of literals be separate?
conjunctLiterals = True

# Use glucose4 as solver
solverId = 'g4'

class PogException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Pog Exception: " + str(self.value)


###
# DEBUGGING support
enableTrace = False
traceIds = []
traceXlits = []
# DEBUGGING support
####

# Integration of SAT solver + RUP proof generator
class Reasoner:
    solver = None
    # Clause categories:
    # 0 Input clause
    # 1 Pseudo-input clause (shadow clause generated for lemma argument)
    # 2 Justification of literal or conflict
    # 3 Intermediate step in justifying literal or conflict
    # Each step is a tuple: Category (0 = input.  Others have higher numbers), Step Id, clause
    stepList = []
    # Dictionary mapping step Ids to position in step list
    stepMap = {}
    # For each category, highest numbered step
    stepMax = {}
    # (Optionally) create dictionary of input clauses mapping tuple of literals to clause Id
    inputClauseMap = {}
    ## Options
    # Saturate for each category before attempting next during unit propagation
    layered = False
    ## Statistics
    satCalls = 0

    def __init__(self, inputClauseList, noSolver = False):
        if noSolver:
            self.solver = None
        else:
            self.solver = Solver(solverId, with_proof = True)
        if mapInputClauseSetting:
            clauseList = [tuple(readwrite.cleanClause(clause)) for clause in inputClauseList]
        else:
            clauseList = inputClauseList
        self.stepList = []
        self.addSolverClauses(clauseList)
        self.stepList = []
        self.stepMap = {}
        self.stepMax = {}
        self.inputClauseMap = {}
        self.satCalls = 0
        cid = 1
        for clause in clauseList:
            self.addStep(0, cid, clause)
            if mapInputClauseSetting:
                self.inputClauseMap[clause] = cid
            cid += 1

    # Add proof step.  Assuming step numbers are always increasing
    def addStep(self, cat, cid, clause):
        idx = len(self.stepList)
        self.stepList.append((cat, cid, clause))
        self.stepMap[cid] = idx
        self.recordCategory(cat, cid)
        return idx

    # Add lemma argument clause
    def addClause(self, cid, clause):
        idx = self.addStep(1, cid, clause)
        self.addSolverClauses([clause])

    # Change category for entry in step list
    def changeCategory(self, idx, ncat):
        (cat, cid, clause) = self.stepList[idx]
        self.stepList[idx] = (ncat, cid, clause)
        self.recordCategory(ncat, cid)

    def getMaxStep(self, cat):
        cid = 1
        for icat in range(cat+1):
            if icat in self.stepMax:
                cid = max(cid, self.stepMax[icat])
        return cid

    # Find clause that is subset of target
    def findClauseId(self, tclause, maxCategory, equal = True):
        if mapInputClauseSetting:
            tclause = readwrite.cleanClause(tclause)
            if tclause in self.inputClauseMap:
                return self.inputClauseMap[tclause]
            if maxCategory == 0 and equal:
                return -1
        maxCid = self.getMaxStep(maxCategory)
        for (cat,cid,clause) in self.stepList:
            if cid > maxCid:
                break
            if cat > maxCategory:
                continue
            if readwrite.testClauseSubset(clause, tclause):
                return cid
        return -1

    # Locate clause associated with step number
    def getClause(self, cid):
        idx = self.stepMap[cid]
        cat,ncid,clause = self.stepList[idx]
        return clause

    # Operations that make use of SAT solver
    def propagate(self, assumptions):
        if self.solver is None:
            raise PogException("Can't call propagate without solver")
        prop, lits = self.solver.propagate(assumptions)
        return prop, lits

    def addSolverClauses(self, clist):
        if self.solver is not None:
            self.solver.append_formula(clist)

    def rupCheck(self, clause):
        if self.solver is None:
            raise PogException("Can't call rupCheck without solver")
        assumptions = readwrite.invertClause(clause)
        prop, slits = self.solver.propagate(assumptions)
        result = not prop
        return result

    def isUnit(self, lit, context):
        ok, lits = self.propagate(context)
        return ok and lit in lits
    
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
            raise PogException("Proof failure.  SAT solver returned invalid proof clause %s" % sclause)
        if len(fields) == 0 or fields[-1] != 0:
            raise PogException("Proof failure.  SAT solver returned invalid proof clause %s" % sclause)
        clause = fields[:-1]
        return clause

    # Core inference engine
    def justifyUnit(self, lit, context):
        clauses =  []
        if lit in context:
            return clauses
        pclause = readwrite.invertClause(context)
        pclause.append(lit)
        if self.solver is None:
            clauses.append(pclause)
            return clauses
        if self.rupCheck(pclause):
            clauses.append(pclause)
            self.addSolverClauses([pclause])
            return clauses
        # Bring out the big guns!
        self.satCalls += 1
        sstate = self.solver.solve(assumptions=context + [-lit])
        if sstate == True:
            print("WARNING. Proof failure. Couldn't justify literal %d with context  %s" % (lit, str(context)))
            raise PogException("Proof failure. Couldn't justify literal %d with context  %s" % (lit, str(context)))
        slist = self.solver.get_proof()
        if len(slist) == 0:
            raise PogException("Proof failure.  SAT solver returned empty proof")
        sclause = slist[-1]
        if len(self.strToClause(sclause)) != 0:
            raise PogException("Proof failure.  Invalid terminator for final step %s" % sclause)
        slist = slist[:-1]
        clauses = []
        # Work backward from end.  Stop when run out of clauses or encounter end of previous proof
        for sclause in reversed(slist):
            clause = self.strToClause(sclause)
            if clause is None:
                continue
            if len(clause) == 0:
                break
            clauses.append(clause)
        clauses.reverse()
        clauses.append(pclause)
        return clauses
    
    #### RUP proof generation code ###
    def recordCategory(self, cat, cid):
        if cat in self.stepMax:
            self.stepMax[cat] = max(self.stepMax[cat], cid)
        else:
            self.stepMax[cat] = cid

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
 
    # Perform one pass of unit propagation through clauses
    # Returns pair of Booleans (found,propagated)
    # Updates search state
    def propagatePass(self, maxCategory, propClauses, propSet, satSet, generatorDict, unitSet):
        maxCid = self.getMaxStep(maxCategory)
        found = False
        propagated = False
        for (cat,cid,clause) in self.stepList:
            if cid > maxCid:
                break
            if cat > maxCategory or cid in propSet or cid in satSet:
                continue
            (uresult, ulit) = self.unitProp(clause, unitSet)
            if uresult == "satisfied":
                satSet.add(cid)
            elif uresult == "unit":
                propagated = True
                propClauses.append(cid)
                propSet.add(cid)
                generatorDict[abs(ulit)] = cid
            elif uresult == "conflict":
                propClauses.append(cid)
                found = True
                break
        return (found, propagated)

    # Try to derive RUP clause chain. Return list of hints
    # Or None if fail
    def findRup(self, tclause, maxCategory):
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

        if self.layered:
            # Work way upward in category
            for mcat in range(maxCategory+1):
                found = False
                propagated = True
                while not found and propagated:
                    found, propagated = self.propagatePass(mcat, propClauses, propSet, satSet, generatorDict, unitSet)
                if found:
                    break
        else:
            found = False
            propagated = True
            while not found and propagated:
                found, propagated = self.propagatePass(maxCategory, propClauses, propSet, satSet, generatorDict, unitSet)

        if found:
            propClauses.reverse()
            usedIdSet = set([propClauses[0]])
            hints = []
            for id in propClauses:
                if id in usedIdSet:
                    hints.append(id)
                    clause = self.getClause(id)
                    for lit in clause:
                        gen = generatorDict[abs(lit)]
                        if gen is not None:
                            usedIdSet.add(gen)
            hints.reverse()
            return hints
        else:
            return None

# Maintain set of clauses, based on simplifications of input clauses
# Augment clause information to manage lemma
# Used to generate and to apply lemma
class Lemma:
    ### Tracking information generated while traversing graph
    # Each entry is tuple (provenance,isOriginal,clause)
    # Provenance is set indicate possible origin clause id's
    # isOriginal indicates whether clause still matches original input clause
    # Clause is input clause that has been simplified by omitting falsified literals
    argList = []
    # Map from clause to position in list
    clauseMap = {}
    # Literals that have been assigned up to this point
    # During the initial pass, this set consists of the intersection of the constraints along
    # all paths to the root node.
    # In conversion to a working lemma, this set restricted to those literals that appear in 
    # an original input clause
    assignedLiteralSet = set([])

    ### Information added for use as lemma
    # Set true once lemma set up and proved
    isLemma = False
    # For each remaining clause, literal of node representing lemma argument
    # Either as negated conjunction of literals or as single literal
    # Set to 0 if clause is an original input clause
    shadowLiterals = []
    # Root node of subgraph
    root = None
    # List of hints generated from lemma proof
    lemmaHints = []
    # List of those literals that were assigned for all paths to subgraph,
    # and which occur in one or more simplified clause
    lemmaSharedContext = []

    # Will have empty input clause list when lemmas are not being generated.
    def __init__(self, inputClauseList):
        cid = 0
        self.argList = []
        self.clauseMap = {}
        self.assignedLiteralSet = set([])
        for clause in inputClauseList:
            cid += 1
            tclause = tuple(clause)
            self.argList.append((set([cid]),True,tclause))
            self.clauseMap[tclause] = cid
        # Stuff reserved for later
        self.isLemma = False
        self.shadowLiterals = []
        self.root = None
        self.lemmaHints = []
        self.lemmaSharedContext = []
    
    # Make fresh copy of tracking information
    def clone(self):
        ncm = Lemma([])
        idx = 0
        for provenance,isOriginal,clause in self.argList:
            ncm.argList.append((set(provenance), isOriginal, clause))
            ncm.clauseMap[clause] = idx
            idx += 1
        ncm.assignedLiteralSet = set(self.assignedLiteralSet)
        return ncm

    def incompatible(self, olemma, reason):
        print("Failing lemma merge.  Lemma=")
        self.show()
        print("Other Lemma=")
        olemma.show()
        raise PogException("Lemma merge failure: %s" % reason)

    # Merge information from another lemma.  Assume have identical clauses (with different provenance)
    # Only accept assigned literals that are common to both
    def merge(self, olemma):
        if len(self.argList) != len(olemma.argList):
            self.incompatible(olemma, "Lemma has %d entries in argList.  Other lemma has %d" % (len(self.argList), len(olemma.argList)))
        # Merge provenances:
        nargList = []
        for provenance,isOriginal,clause in self.argList:
            if clause not in olemma.clauseMap:
                self.incompatible(olemma, "Clause %s in lemma not present in other lemma" % str(clause))
            oidx = olemma.clauseMap[clause]
            oprovenance,oisOriginal,oclause = olemma.argList[oidx]
            nprovenance = provenance | oprovenance
            nisOriginal = isOriginal and oisOriginal
            nargList.append((nprovenance,nisOriginal,clause))
        self.argList = nargList
        self.assignedLiteralSet &= olemma.assignedLiteralSet            
        return

    # Assign value to literal
    # Eliminate satisfied clauses
    def assignLiteral(self, lit):
        self.assignedLiteralSet.add(lit)
        nargList = []
        idx = 0
        self.clauseMap = {}
        for provenance,isOriginal,clause in self.argList:
            if lit in clause:
                continue
            elif -lit in clause:
                isOriginal = False
                clause = tuple([nlit for nlit in clause if nlit != -lit])
            self.clauseMap[clause] = idx
            nargList.append((provenance,isOriginal,clause))
            idx += 1
        self.argList = nargList


    # Consider only clauses with variables in vset
    # Assume given clause either fully in or fully excluded from vset
    def restrictVariables(self, vset):
        nargList = []
        idx = 0
        self.clauseMap = {}
        for tup in self.argList:
            provenance,isOriginal,clause = tup
            if (len(clause)) > 0 and abs(clause[0]) in vset:
                self.clauseMap[clause] = idx
                nargList.append(tup)
                idx += 1
        self.argList = nargList

    def setupLemma(self, root, pog):
        self.shadowLiterals = []
        # Derive subset of the assigned literals that occur in at least one original input clause
        # These become part of context for lemma
        externalLiteralSet = set([])
        self.root = root
        for idx in range(len(self.argList)):
            provenance,isOriginal,clause = self.argList[idx]
            # Find what literals get used
            if not isOriginal:
                for icid in provenance:
                    iclause = pog.inputClauseList[icid-1]
                    for lit in iclause:
                        if lit in self.assignedLiteralSet:
                            externalLiteralSet.add(lit)
            if isOriginal:
                lit = 0
                if len(provenance) != 1:
                    raise PogException("Setting up Lemma %s. Lemma thinks there's a unique input clause, but the provenance is %s" %
                                       str(root), str(provenance))
                icid = list(provenance)[0]
                pog.addComment("Lemma %s, argument #%d: input clause %d" % (str(root), idx+1, icid))
            elif len(clause) == 1:
                # Don't expect this to happen, since would have unit propagation
                lit = clause[0]
                pog.addComment("Lemma %s, argument #%d: Shadow literal %d" % (str(root), idx+1, lit))
            else:
                children = [pog.findNode(-lit) for lit in clause]
                node = pog.addConjunction(children, forLemma = True)
                if node.definingClauseId is None:
                    cid = pog.cwriter.finalizeAnd(node.ilist, node.xlit)
                    node.definingClauseId = cid
                    shadowClause = readwrite.cleanClause(readwrite.invertClause(node.ilist) + [node.xlit])
                    pog.reasoner.addClause(cid, shadowClause)
                lit = -node.xlit
                pog.addComment("Lemma %s, argument #%d: shadow clause #%d, possible input clauses: %s" % (str(root), idx+1, node.definingClauseId, str(provenance)))
            self.shadowLiterals.append(lit)
        self.assignedLiteralSet = externalLiteralSet


    def getIdx(self, clause):
        if clause not in self.clauseMap:
            raise PogException("Problem in applying lemma.  Can't find shadow node matching argument clause %s" % (str(clause)))
        return self.clauseMap[clause]


    # Given clause, find associated shadow literal
    def findShadowLiteral(self, clause):
        idx = self.getIdx(clause)
        return self.shadowLiterals[idx]

    # Given clause, find originating input clause
    def findInputClause(self, clause):
        idx = self.getIdx(clause)
        provenance,isOriginal,xclause = self.argList[idx]
        # Matching input clause need not be unique
        icid = list(provenance)[0]
        return icid
    
    def show(self):
        print("Assigned literals: %s" % str(sorted(self.assignedLiteralSet)))
        for provenance,isOriginal,clause in self.argList:
            print("Clause %s.  From input clause(s) #%s.  Original? %s" % (str(clause), str(provenance), str(isOriginal)))


class NodeType:
    tcount = 5
    tautology, variable, negation, conjunction, disjunction = range(5)
    typeName = ["taut", "var", "neg", "conjunct", "disjunct"]

class DeletionMarkType:
    markNew, markFound, markNone = range(3)


# Prototype node.  Used for unique table lookup
class ProtoNode:
    ntype = None
    children =  None

    def __init__(self, ntype, children):
        self.ntype = ntype
        self.children = children

    def key(self):
        return tuple([self.ntype] + [c.xlit for c in self.children])

    def isOne(self):
        return self.ntype == NodeType.tautology

    def isZero(self):
        return self.ntype == NodeType.negation and self.children[0].isOne()

    def isConstant(self):
        return self.isOne() or self.isZero()


  

class Node(ProtoNode):
    # For traversals
    mark = False 
    # Graph properties
    indegree = 0
    height = 0

    xlit = None
    # Information used during proof generation.  Holdover from when node represented ITE
    iteVar = None
    # Variables on which this depends
    dependencySet = set([])
    # Id of first clause in defining clauses
    definingClauseId = None
    # Id of clause that validates this as potential root node
    unitClauseId = None
    # Stash away argument list of And or Or node
    ilist = None
    # Stash away hints for Or node
    hints = None
    # Pointer to lemma if have one
    lemma = None
 
    def __init__(self, xlit, ntype, children):
        ProtoNode.__init__(self, ntype, children)
        self.xlit = xlit
        self.iteVar = None
        self.dependencySet = set([])
        for child in children:
            self.dependencySet |= child.dependencySet
        self.definingClauseId = None
        self.unitClauseId = None
        self.mark = False
        self.doDegreeHeight()
        self.ilist = None
        self.hintPairs = None
        self.lemma = None
        
    
    def doDegreeHeight(self):
        self.indegree = 0
        self.height = 0
        if self.ntype == NodeType.negation:
            self.height = self.children[0].height
            return
        for child in self.children:
            if child.ntype == NodeType.negation:
                child.children[0].indegree += 1
            else:
                child.indegree += 1
        if len(self.children) > 0:
            cheight = max(child.height for height in self.children)
            self.height = cheight+1

    # Criteria for constructing lemma
    def wantLemma(self, lemmaHeight):
        if lemmaHeight is None:
            return False
        return self.indegree > 1 and self.height >= lemmaHeight

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

    literalGroup = False

    def __init__(self, children, xlit):
        Node.__init__(self, xlit, NodeType.conjunction, children)
        self.ilist = [child.xlit for child in children]
        self.literalGroup = False

    def __str__(self):
        return "P%d" % self.xlit

class Disjunction(Node):

    def __init__(self, child1, child2, xlit, hintPairs):
        Node.__init__(self, xlit, NodeType.disjunction, [child1, child2])
        self.ilist = [child1.xlit, child2.xlit]
        self.hintPairs = hintPairs

    def __str__(self):
        return "S%d" % self.xlit

# Represent overall POG
class Pog:
    
    # Constant Nodes
    leaf1 = None
    leaf0 = None
    # Mappings (ntype, arg1, ..., argk) to nodes
    uniqueTable = {}
    uniqueArgTable = {}
    # All Nodes
    nodes = []
    # Mapping from xlit to node
    nodeMap = {}
    # Verbosity level
    verbLevel = 1
    cwriter = None
    inputClauseList = []
    reasoner = None
    # Options
    # Should the program attempt to fill out all hints?
    hintLevel = 2
    # What is minimum height for shared subgraph to generate lemma (None--> no lemmas)
    lemmaHeight = None
    # Statistics:
    # Count of each node by type
    nodeCounts = []
    # Traverses of nodes by type
    nodeVisits = []
    # Total number of defining clauses
    definingClauseCounts = 0
    # Added RUP clause counts, indexed by number of clauses to justify single literal
    literalClauseCounts = {}
    # Added RUP clause counts, indexed by node type
    nodeClauseCounts = []
    # Number of lemmas and applications
    lemmaCount = 0
    lemmaShadowNodeCount = 0
    lemmaShadowNodeClauseCount = 0
    lemmaApplicationCount = 0
    lemmaApplicationClauseCount = 0

    def __init__(self, variableCount, inputClauseList, fname, verbLevel, hintLevel, splitMode, lemmaHeight):
        self.verbLevel = verbLevel
        self.hintLevel = hintLevel
        self.lemmaHeight = lemmaHeight
        self.uniqueTable = {}
        self.uniqueArgTable = {}
        self.inputClauseList = readwrite.cleanClauses(inputClauseList)
        self.cwriter = readwrite.CratWriter(variableCount, inputClauseList, fname, verbLevel)
        self.reasoner = Reasoner(inputClauseList, noSolver = splitMode >= 2)
        self.nodeCounts = [0] * NodeType.tcount
        self.nodeVisits = [0] * NodeType.tcount
        self.definingClauseCounts = 0
        self.literalClauseCounts = {1:0}
        self.nodeClauseCounts = [0] * NodeType.tcount
        self.lemmaCount = 0
        self.lemmaShadowNodeCount = 0
        self.lemmaShadowNodeClauseCount = 0
        self.lemmaApplicationCount = 0
        self.lemmaApplicationClauseCount = 0

        self.leaf1 = One()
        self.store(self.leaf1)
        self.leaf0 = Negation(self.leaf1)
        self.store(self.leaf0)
        for i in range(1, variableCount+1):
            v = Variable(i)
            self.store(v)
            self.addNegation(v)
        
    def lookup(self, ntype, children, forLemma = False):
        n = ProtoNode(ntype, children)
        key = n.key()
        if forLemma:
            if key in self.uniqueArgTable:
                return self.uniqueArgTable[key]
        else:
            return None
            if key in self.uniqueTable:
                return self.uniqueTable[key]
        return None

    # Return node with associated xlit
    def findNode(self, xlit):
        if xlit not in self.nodeMap:
            raise PogException("No node with xlit %d" % xlit)
        return self.nodeMap[xlit]

    def store(self, node, forLemma=False):
        key = node.key()
        if forLemma:
            self.uniqueArgTable[key] = node
        else:
            self.uniqueTable[key] = node
            self.nodes.append(node)
        self.nodeMap[node.xlit] = node

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

    def addConjunction(self, children, forLemma = False, fromIte = False):
        nchildren = []
        for child in children:
            nchildren = self.mergeConjunction(child, nchildren)
        if type(nchildren) == type(self.leaf0) and nchildren == self.leaf0:
            return nchildren
        # Make sure nonterminal children follow literals
        lchildren = []
        ntchildren = []
        for c in nchildren:
            if c.getLit() is None:
                ntchildren.append(c)
            else:
                lchildren.append(c)
        children = lchildren + ntchildren
        if conjunctLiterals and fromIte and len(lchildren) > 2 and len(ntchildren) > 0:
            # Create special conjunction for all but first literal
            ln = self.addConjunction(lchildren[1:])
            ln.literalGroup = True
            children =  [lchildren[0], ln] + ntchildren
        n = self.lookup(NodeType.conjunction, children, forLemma=forLemma)
        if n is None:
            xlit = self.cwriter.newXvar()
            n = Conjunction(children, xlit)
            self.store(n, forLemma)
        if forLemma:
            self.lemmaShadowNodeCount += 1
            self.lemmaShadowNodeClauseCount += len(children) + 1
        return n

    def addDisjunction(self, child1, child2, hintPairs = None):
        if child1.isOne() or child2.isOne():
            return self.leaf1
        if child1.isZero():
            return child2
        if child2.isZero():
            return child1
        n = self.lookup(NodeType.disjunction, [child1, child2])
        if n is None:
            xlit = self.cwriter.newXvar()
            n = Disjunction(child1, child2, xlit, hintPairs)
            self.store(n)
        return n

    # Find information to generate hint for mutual exclusion proof
    def findHintPair(self, node, var):
        if node.ntype != NodeType.conjunction:
            return None
        for idx in range(len(node.children)):
            child = node.children[idx]
            if abs(child.xlit) == var:
                return (node, idx+1)
        return None

    def addIte(self, nif, nthen, nelse):
        if nif.isOne():
            result = nthen

        elif nif.isZero():
            result = nelse
#        This is a valid rule, but applying it makes proof generation difficult
#        elif nthen == nelse:
#            result = nthen
        elif nthen.isOne() and nelse.isZero():
            result = nif
        elif nthen.isZero() and nelse.isOne():
            result = self.addNegation(nif)
        elif nthen.isOne():
            result = self.addNegation(self.addConjunction([self.addNegation(nif), self.addNegation(nelse)]))
        elif nthen.isZero():
            result = self.addConjunction([self.addNegation(nif), nelse])
        elif nelse.isOne():
            result = self.addNegation(self.addConjunction([nif, self.addNegation(nthen)]))
        elif nelse.isZero():
            result = self.addConjunction([nif, nthen])
        else:
            ntrue = self.addConjunction([nif, nthen], fromIte = True)
            nfalse = self.addConjunction([self.addNegation(nif), nelse], fromIte = True)
            hint1 = self.findHintPair(ntrue, nif.xlit)
            hint2 = self.findHintPair(nfalse, nif.xlit)
            if hint1 is None or hint2 is None:
                hints = None
            else:
                hints = [hint1, hint2]
            n = self.addDisjunction(ntrue, nfalse, hints)
            result = n
        result.iteVar = nif.xlit
        if self.verbLevel >= 3:
            print("ITE(%s, %s, %s) --> %s" % (str(nif), str(nthen), str(nelse), str(result)))
        return result

    def addComment(self, s, lowerSplit = False):
        self.cwriter.doComment(s, lowerSplit)

    def deleteClause(self, id, hlist = None):
        self.cwriter.doDeleteClause(id, hlist)

    def deleteOperation(self, node):
        self.cwriter.doDeleteOperation(node.xlit, node.definingClauseId, 1+len(node.children))
        
    def validateDisjunction(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        hints = []
        if root.iteVar is None:
            raise PogException("Don't know how to validate OR node %s that is not from ITE" % str(root))
        svar = root.iteVar
        # Recursively validate children
        thints = self.validateUp(root.children[0], context + [svar], root) 
        fhints =  self.validateUp(root.children[1], context + [-svar], root)
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
        hints = [cid]
        self.nodeClauseCounts[root.ntype] += 2
        if len(context) == 0:
            root.unitClauseId = cid
        return hints

    def validateUnit(self, lit, context):
        hints = []
        if self.verbLevel >= 3:
            print("Validating unit %d in context %s" % (lit, str(context)))
        if lit in context:
            if self.verbLevel >= 3:
                print("Unit literal %d already in context %s" % (lit, str(context)))
            return hints
        if self.hintLevel >= 2:
            # See if can find matching input clause
            tclause = [lit] + readwrite.invertClause(context)
            cid = self.reasoner.findClauseId(tclause, maxCategorySetting, equal = True)
            if cid > 0:
                if self.verbLevel >= 3:
                    print("Found input/argument clause #%d=%s justifying unit literal %d in context %s.  Adding as hint" % (cid, self.reasoner.getClause(cid), lit, str(context)))
                hints.append(cid)
                return hints
        if self.hintLevel >= 3:
            # See if can generate RUP proof over input and lemma argument clauses
            tclause = [lit] + readwrite.invertClause(context)
            rhints = self.reasoner.findRup(tclause, 1)
            if rhints is not None:
                if len(rhints) == 1:
                    # Found matchingclause
                    cid = rhints[0]
                    if self.verbLevel >= 3:
                        print("Found input/argument clause #%d=%s justifying unit literal %d in context %s.  Adding as hint" % (cid, self.reasoner.getClause(cid), lit, str(context)))
                    hints.append(cid)
                    return hints
                if self.verbLevel >= 3:
                    print("Justified unit literal %d in context %s with single RUP step and hints %s" % (lit, str(context), str(rhints)))
                if self.verbLevel >= 2:
                    self.addComment("Justify literal %d in context %s with single RUP step" % (lit, str(context)))
                cid = self.cwriter.doClause(tclause, rhints)
                self.literalClauseCounts[1] += 1
                self.reasoner.addStep(2, cid, tclause)
                hints.append(cid)
                return hints
        clauses = self.reasoner.justifyUnit(lit, context)
        lastCid = None
        idxList = []
        if self.hintLevel >= 4:
            self.addComment("Justify literal %d in context %s with %d hinted steps" % (lit, str(context), len(clauses)))
            for clause in clauses:
                # Should be able to justify each clause
                rhints = self.reasoner.findRup(clause, 3)
                if rhints is None:
                    raise PogException("Failed to justify intermediate clause %s when trying to justify literal %d in context %s" % (str(clause), lit, str(context)))
                cid = self.cwriter.doClause(clause, rhints)
                if self.verbLevel >= 3:
                    print("Generated hints for intermediate clause #%d" % (cid))
                idxList.append(self.reasoner.addStep(1, cid, clause))
                lastCid = cid
        else:
            self.addComment("Justify literal %d in context %s with %d unhinted steps" % (lit, str(context), len(clauses)), lowerSplit = True)
            for clause in clauses:
                cid = self.cwriter.doClause(clause, splitLower = True)
                if self.verbLevel >= 3:
                    print("Require hints for intermediate clause #%d" % (cid))
                idxList.append(self.reasoner.addStep(1, cid, clause))
                lastCid = cid
        hints.append(lastCid)
        if self.verbLevel >= 3:
            print("Added hint %d" % lastCid)
        # Change categories for all added clauses, except for last one
        idxList = idxList[:-1]
        for idx in idxList:
            self.reasoner.changeCategory(idx, 3)
        if self.verbLevel >= 3:
            print("Justified unit literal %d in context %s with %d proof steps" % (lit, str(context), len(clauses)))

        nc = len(clauses)
        if nc in self.literalClauseCounts:
            self.literalClauseCounts[nc] += 1
        else:
            self.literalClauseCounts[nc] = 1
        return hints


    def validateConjunction(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        hints = []
        vcount = 0
        ncontext = list(context)
       
        if root.literalGroup:
            if self.verbLevel >= 3:
                print("Validating literal conjunction node %s in context %s" % (str(root), str(context)))
            # Validate entire conjunction
            hints = self.validateUnit(root.xlit, ncontext)
            hints += [root.definingClauseId+1+i for i in range(len(root.children))]
            return hints

        if self.verbLevel >= 3:
            print("Validating conjunction node %s in context %s" % (str(root), str(context)))

        for c in root.children:
            clit = c.getLit()
            if clit is None:
                chints = self.validateUp(c, ncontext, root)
                hints += chints
                vcount += 1
                if self.verbLevel >= 3:
                    print("Got hints %s from child %s" % (str(chints), str(c)))
                if c.ntype == NodeType.conjunction:
                    # Can add literals to context
                    for gc in c.children:
                        glit = gc.getLit()
                        if glit is not None:
                            if glit not in ncontext:
                                ncontext.append(glit)
                            if root.lemma is not None:
                                root.lemma.assignLiteral(glit)
            else:
                if root.lemma is not None:
                    root.lemma.assignLiteral(clit)
                chints = self.validateUnit(clit, ncontext)
                hints += chints
                if clit not in ncontext:
                    ncontext.append(clit)
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
            hints = [cid]
            if self.verbLevel >= 3:
                print("Asserted unit clause for AND node %s%s.  Clause #%d" % (str(root), rstring, cid))
            self.nodeClauseCounts[root.ntype] += 1
        else:
            hints.append(root.definingClauseId)
            if self.verbLevel >= 3:
                print("Returned hints from AND node %s%s Hints:%s" % (str(root), rstring, str(hints)))
        if len(context) == 0:
            root.unitClauseId = cid
        return hints

    # Negated conjunction represents partial clause
    def validateNegatedConjunction(self, root, context, parent):
        nroot = root.children[0]
        rstring = " (root)" if parent is None else ""
        hints = []
        # Gather children
        lits = []
        # Can have at most one nonterminal child
        ntchild = None
        for child in nroot.children:
            lit = child.getLit()
            if lit is None:
                # Nonterminal child
                ntchild = child
            else:
                lits.append(lit)
        clause = [root.xlit] + readwrite.invertClause(context)
        if self.hintLevel >= 2:
            if ntchild is None:
                tclause = readwrite.invertClause(lits + context)
                lcid = self.reasoner.findClauseId(tclause, maxCategorySetting, equal = False)
                if lcid <= 0:
                    raise PogException("Couldn't find input clause %s represented by negated conjunction %s" % (str(tclause), str(root)))
            else:
                # Nonterminal child must be negated
                if ntchild.ntype == NodeType.negation:
                    nntchild = ntchild.children[0]
                    chints = self.validateUp(nntchild, context + lits, ntchild)
                    lcid = chints[0]
                else:
                    raise PogException("Don't know how to generate proof for node %s.  It has non-negated nonterminal child %s" % (str(root), str(ntchild)))
            hints = [nroot.definingClauseId+1+i for i in range(len(nroot.children))]
            hints.append(lcid)
            if self.verbLevel >= 2:
                self.addComment("Assert clause for negated disjunction %s%s" % (str(root), rstring))
            cid = self.cwriter.doClause(clause, hints)
        else:
            if ntchild is not None:
                # Nonterminal child must be negated
                if ntchild.ntype == NodeType.negation:
                    nntchild = ntchild.children[0]
                    self.validateUp(nntchild, context + lits, ntchild)
                else:
                    raise PogException("Don't know how to generate proof for node %s.  It has non-negated nonterminal child %s" % (str(root), str(ntchild)))
            if self.verbLevel >= 2:
                self.addComment("Assert clause for negated disjunction %s%s" % (str(root), rstring))
            cid = self.cwriter.doClause(clause)
        self.nodeClauseCounts[root.ntype] += 1
        hints = [cid]
        if len(context) == 0:
            root.unitClauseId = cid
        return hints

    # Construct lemma
    def generateLemma(self, root):
        # Set up lemma for this node
        self.addComment("Prove Lemma %s" % str(root))
        ncontext = [lit for lit in root.lemma.shadowLiterals if lit != 0] 
        ncontext += list(root.lemma.assignedLiteralSet)
        root.lemma.isLemma = True
        # Prove the lemma
        hints = self.validateUp(root, ncontext, None)
        self.addComment("Completed proof of Lemma %s.  Assumed literals = %s" % (str(root), str(ncontext)))
        root.lemma.lemmaHints = hints
        self.lemmaCount += 1


    def applyLemma(self, root, context, callingLemma):
        # Apply lemma
        self.addComment("Apply Lemma %s.  Context = %s" % (str(root), str(context)))
        # Show that each shadow literal activated
        idx = 0
        lcontext = context
        lhints = []
        for lit in root.lemma.assignedLiteralSet:
            if lit not in lcontext:
                self.addComment("Lemma %s.  Justify assigned literal %d in context %s" % (str(root), lit, str(lcontext)))
                chints = self.validateUnit(lit, lcontext)
                lhints += chints
                lcontext.append(lit)
        for provenance,isOriginal,clause in root.lemma.argList:
            idx += 1
            if isOriginal:
                continue
            lit = root.lemma.findShadowLiteral(clause)
            if lit in lcontext:
                self.addComment("Lemma argument #%d (clause %s) already activated by literal %d" % (idx, str(clause), lit))
                continue
            aclause = readwrite.invertClause(lcontext) + [lit]
            icid = callingLemma.findInputClause(clause)
            iclause = self.inputClauseList[icid-1]
            self.addComment("Lemma argument #%d (clause %s) from input clause #%d:%s" % (idx, str(clause), icid, str(iclause)))
            if self.hintLevel >= 2:
                # Track down hints for this argument
                ahints = []
                alits = []
                anode = self.findNode(-lit)
                if anode.ntype == NodeType.conjunction:
                    pos = anode.definingClauseId + 1
                    for alit in anode.ilist:
                        if -alit in iclause:
                            ahints.append(pos)
                            alits.append(alit)
                        pos += 1
                # See if there are other literals that must be justified
                ncontext = lcontext + alits
                conflict = False
                for lit in iclause:
                    if -lit not in ncontext and lit not in clause and -lit not in alits and -lit not in root.lemma.assignedLiteralSet:
                        self.addComment("Lemma %s.  Justify additional literal %d from input clause %d in context %s" % (str(root), -lit, icid, str(ncontext)))
                        chints = self.validateUnit(-lit, ncontext)
                        if len(chints) == 1 and chints[0] == ahints[-1]:
                            conflict = True
                            break
                        ahints += chints
                        ncontext.append(-lit)
                if not conflict:
                    ahints += [icid]
                lhints.append(self.cwriter.doClause(aclause, ahints))
            else:
                self.cwriter.doClause(aclause)
            self.lemmaApplicationClauseCount += 1
        self.addComment("Lemma invocation")
        lclause = readwrite.invertClause(context) + [root.xlit]
        if self.hintLevel >= 2:
            lhints += root.lemma.lemmaHints
            cid = self.cwriter.doClause(lclause, lhints)
            hints = [cid]
        else:
            self.cwriter.doClause(lclause)
            hints = []
        self.lemmaApplicationClauseCount += 1
        self.lemmaApplicationCount += 1
        return hints

    def checkHints(self, root, context, hints):
        for id in hints:
            if type(id) != type(1):
                raise PogException("Validation of node %s in context %s.  Bad hint generated: '%s'" % (str(root), str(context), str(id)))
        


    # Generate justification of root nodes
    # context is list of literals that are assigned in the current context
    # Returns list of unit clauses that should be deleted
    def validateUp(self, root, context, parent = None):
        if parent is not None and root.lemma is not None:
            if root.lemma.isLemma:
                return self.applyLemma(root, context, parent.lemma)
            elif root.wantLemma(self.lemmaHeight):
                self.generateLemma(root)
                return self.applyLemma(root, context, parent.lemma)

        self.nodeVisits[root.ntype] += 1
        if root.ntype == NodeType.disjunction:
            return self.validateDisjunction(root, context, parent)
        elif root.ntype == NodeType.conjunction:
            return self.validateConjunction(root, context, parent)
        elif root.ntype == NodeType.negation and root.children[0].ntype == NodeType.conjunction:
            return self.validateNegatedConjunction(root, context, parent)
        else:
            raise PogException("Don't know how to validate node %s" % str(root))
                

    def validateUpChecking(self, root, context, parent = None):
        hints = self.validateUpCore(root, context, parent)
        self.checkHints(root, context, hints)
        return hints

    def deletionHintsConjunction(self, root, clause):
        trace = enableTrace and root.xlit in traceXlits
        if trace:
            print("Tracing deletion hints for conjunction %s" % str(root))
        for idx in range(len(root.children)):
            child = root.children[idx]
            lit = child.getLit()
            if lit is None:
                vset = set([abs(lit) for lit in clause])
                if len(vset & child.dependencySet) > 0:
                    hints = self.deletionHints(child, clause, noneOk = True)
                    if hints is None:
                        continue
                    hints.append(root.definingClauseId+1+idx)
                    if trace:
                        print("    Got hints %s from nonliteral child %s" % (str(hints), str(child)))
                    return hints
                else:
                    continue
            else:
                if lit in clause:
                    hints = [root.definingClauseId+1+idx]
                    if trace:
                        print("    Got hints %s from literal child %s" % (str(hints), str(child)))
                    return hints
                else:
                    continue
        # May reach here when have literals combined into conjunction
        # Otherwise, will flag error when return
        if trace:
            print("    Got None")
        return None


    # Want conjunction to yield true, so that its negation is false
    def deletionHintsNegatedConjunction(self, root, clause):
        nroot = root.children[0]
        hlist = []
        for idx in range(len(nroot.children)):
            child = nroot.children[idx]
            lit = child.getLit()
            if lit is None:
                # child must be negation
                if child.ntype == NodeType.negation:
                    nchild = child.children[0]
                    hlist += self.deletionHints(nchild, clause)
                else:
                    raise PogException("Couldn't justify deletion of clause %s.  Negated conjunction %s has non-negated nonterminal child %s" % (str(clause), str(root), str(child)))
            else:
                if -lit not in clause:
                    raise PogException("Couldn't justify deletion of clause %s.  Negated conjunction %s contains unhandled literal %d" % (str(clause), str(root), lit))
        # Checks out
        hlist.append(nroot.definingClauseId)
        return hlist

    def deletionHintsDisjunction(self, root, clause):
        hlist = []
        for child in root.children:
            chints = self.deletionHints(child, clause)
            if chints is None:
                print("Uh-oh.  Calling deletion hints from %s gave child call on %s, which returned None" % (str(root), str(child)))
                raise PogException("Couldn't justify deletion of clause %s." % (str(clause)))
            else:
                hlist += chints

        hlist.append(root.definingClauseId)
        return hlist

    # Generate list of hints to justify deletion of clause
    # Make sure all paths compatible with negating assignment lead to false
    # Raise error if cannot justify
    def deletionHints(self, root, clause, noneOk = False):
        hints = []
        # Only need result from single visit to node
        if root.mark == DeletionMarkType.markFound:
            return []
        if root.mark == DeletionMarkType.markNone:        
            return None
        root.mark = DeletionMarkType.markFound
        if root.ntype == NodeType.conjunction:
            hints = self.deletionHintsConjunction(root, clause)
            if hints is None:
                if noneOk:
                    root.mark = DeletionMarkType.markNone
                else:
                    raise PogException("Couldn't justify deletion of clause %s.  Reached compatible conjunction %s" % (str(clause), str(root)))
        elif root.ntype == NodeType.disjunction:
            hints = self.deletionHintsDisjunction(root, clause)
        elif root.isZero():
            pass
        elif root.isOne():
            raise PogException("Couldn't justify deletion of clause %s.  Reached terminal constant 1" % str(clause))
        elif root.ntype == NodeType.negation:
            nchild = root.children[0]
            if nchild.ntype == NodeType.conjunction:
                hints = self.deletionHintsNegatedConjunction(root, clause)
            elif nchild.ntype == NodeType.variable:
                lit = root.getLit()
                if lit in clause:
                    pass
                else:
                    raise PogException("Couldn't justify deletion of clause %s.  Reached terminal literal %s" % (str(clause), str(root))) 
            else:
                raise PogException("Couldn't justify deletion of clause %s.  Reached negated node with unhandled type %s" % (str(clause), str(nchild))) 
        else:
            lit = root.getLit()
            if lit is None:
                raise PogException("Couldn't justify deletion of clause %s.  Reached node with unknown type %s" % (str(clause), str(root))) 
            if lit in clause:
                pass
            else:
                raise PogException("Couldn't justify deletion of clause %s.  Reached terminal literal %s" % (str(clause), str(root))) 
        if enableTrace:
            print("deletionHints(%s,%s) --> %s" % (str(root), str(clause), str(hints)))
        return hints

    def doValidate(self):
        global enableTrace
        root = self.nodes[-1]
        hints = self.validateUp(root, [], parent = None)
        topUnitId = root.unitClauseId
        if self.verbLevel >= 2:
            self.addComment("Delete all but final asserted clause")
        self.cwriter.doDeleteAssertedClauses()
        if self.verbLevel >= 2:
            self.addComment("Delete input clauses")
        for cid in range(1, len(self.inputClauseList)+1):
            enableTrace = cid in traceIds
            for node in self.nodes:
                node.mark = DeletionMarkType.markNew
            if self.hintLevel >= 1:
                hints = self.deletionHints(root, self.inputClauseList[cid-1])
                hints.append(topUnitId)
            else:
                hints = None
            self.deleteClause(cid, hints)
            
    def finish(self):
        self.cwriter.finish()
        if self.verbLevel >= 1:
            nnode = 0
            ndclause = self.definingClauseCounts
            print("GEN: Nodes by type")
            for t in range(NodeType.tcount):
                if self.nodeCounts[t] == 0:
                    continue
                print("GEN:    %s: %d" % (NodeType.typeName[t], self.nodeCounts[t]))
                nnode += self.nodeCounts[t]
            print("GEN:   POG TOTAL: %d" % nnode)
            print("GEN: Total defining clauses: %d" % ndclause)
            nvnode = 0
            print("GEN: Node visits during proof generation (by node type)")
            for t in range(NodeType.tcount):
                if self.nodeVisits[t] == 0:
                    continue
                print("GEN:    %s: %d" % (NodeType.typeName[t], self.nodeVisits[t]))
                nvnode += self.nodeVisits[t]
            print("GEN:   VIS TOTAL: %d" % nvnode)
            nldclause = self.lemmaShadowNodeClauseCount
            nlaclause = self.lemmaApplicationClauseCount
            if self.lemmaCount > 0:
                print("GEN: Lemmas:  %d definitions.  %d shadow nodes (%d defining clauses), %d applications" % 
                      (self.lemmaCount, self.lemmaShadowNodeCount, nldclause, self.lemmaApplicationCount))
            nlclause = 0
            print("GEN: Calls to SAT Solver: %d" % self.reasoner.satCalls)
            print("GEN: Literal justification clause counts (by number of clauses in justification:")
            singletons = []
            for count in sorted(self.literalClauseCounts.keys()):
                nc = self.literalClauseCounts[count]
                nlclause += count * nc
                if nc == 1:
                    singletons.append(str(count))
                else:
                    print("GEN:    %d : %d" % (count, nc))
            if len(singletons) > 1:
                print("GEN:    1 each for counts %s" % ", ".join(singletons))
            print("GEN:   LIT TOTAL: %d" % nlclause)
            nnclause = 0
            print("GEN: RUP clauses for node justification (by node type):")
            for t in range(NodeType.tcount):
                if self.nodeClauseCounts[t] == 0:
                    continue
                print("GEN:    %s: %d" % (NodeType.typeName[t], self.nodeClauseCounts[t]))
                nnclause += self.nodeClauseCounts[t]
            print("GEN:   RUP TOTAL: %d" % nnclause)
            niclause = len(self.inputClauseList)
            nclause = niclause + ndclause + nldclause + nlaclause + nlclause + nnclause
            print("GEN: Total clauses: %d input + %d defining + %d lemma defining + %d lemma application + %d literal justification + %d node justifications = %d" % (niclause, ndclause, nldclause, nlaclause, nlclause, nnclause, nclause))

    def doMark(self, root):
        if root.mark:
            return
        root.mark = True
        for c in root.children:
            self.doMark(c)
        
    # Perform mark & sweep to remove any nodes not reachable from root
    # Generate node declarations
    # Construct context sets
    def finalize(self, splitMode):
        for node in self.nodes:
            node.mark = False
        root = self.nodes[-1]
        self.doMark(root)
        nnodes = []

        # Generate compressed set of nodes.
        for node in self.nodes:
            if not node.mark:
                continue
            self.nodeCounts[node.ntype] += 1
            node.doDegreeHeight()
            nnodes.append(node)
        self.nodes = nnodes

        if self.lemmaHeight is not None:
            self.addLemmas()

        # Generate node declarations
        # Must do in two passes, with conjunction nodes coming earlier
        for node in self.nodes:
            if node.ntype == NodeType.conjunction and node.literalGroup:
                if self.verbLevel >= 2:
                    slist = [str(child) for child in node.children]
                    self.addComment("%s = AND(%s)" % (str(node), ", ".join(slist)))
                cid = self.cwriter.finalizeAnd(node.ilist, node.xlit)
                node.definingClauseId = cid
                self.definingClauseCounts += 1 + len(node.children)
                pclause = readwrite.cleanClause(readwrite.invertClause(node.ilist) + [node.xlit])
                self.reasoner.addClause(cid, pclause)

        if splitMode > 0:
            self.cwriter.split()


        for node in self.nodes:
            if node.ntype == NodeType.conjunction and not node.literalGroup:
                if self.verbLevel >= 2:
                    slist = [str(child) for child in node.children]
                    self.addComment("%s = AND(%s)" % (str(node), ", ".join(slist)))
                cid = self.cwriter.finalizeAnd(node.ilist, node.xlit)
                node.definingClauseId = cid
                self.definingClauseCounts += 1 + len(node.children)
            elif node.ntype == NodeType.disjunction:
                if self.verbLevel >= 2:
                    self.addComment("%s = OR(%s, %s)" % (str(node), str(node.children[0]), str(node.children[1])))
                hints = None
                if node.hintPairs is not None and self.hintLevel >= 1:
                    hints = [node.definingClauseId+offset for node,offset in node.hintPairs]
                node.definingClauseId = self.cwriter.finalizeOr(node.ilist, node.xlit, hints)
                self.definingClauseCounts += 1 + len(node.children)
            elif node.ntype == NodeType.negation:
                node.definingClauseId = node.children[0].definingClauseId
                


    def addLemmas(self):
        root = self.nodes[-1]
        root.lemma = Lemma(self.inputClauseList)
        self.addComment("Negated conjunction operations to use as lemma arguments")
        for node in reversed(self.nodes):
            if node.ntype not in [NodeType.conjunction, NodeType.disjunction]:
                continue
            if node.wantLemma(self.lemmaHeight):
                node.lemma.setupLemma(node, self)
            elif not node.lemma:
                continue
            ntchildren = []
            nlemma = node.lemma.clone()
            if node.ntype == NodeType.conjunction:
                for child in node.children:
                    clit = child.getLit()
                    if clit is None:
                        if child.ntype in [NodeType.conjunction, NodeType.disjunction]:
                            ntchildren.append(child)
                        if child.ntype == NodeType.conjunction:
                            for gchild in child.children:
                                glit = gchild.getLit()
                                if glit is not None:
                                    nlemma.assignLiteral(glit)
                    else:
                        nlemma.assignLiteral(clit)
            else:
                for child in node.children:
                    if child.ntype in [NodeType.conjunction, NodeType.disjunction]:
                        ntchildren.append(child)
            clemmas = []
            # Make separate copies of lemma for each child
            for i in range(len(ntchildren)-1):
                clemmas.append(nlemma.clone())
            clemmas.append(nlemma)
            restrict = node.ntype == NodeType.conjunction and len(ntchildren) > 0
            for (child,lemma) in zip(ntchildren,clemmas):
                if restrict:
                    lemma.restrictVariables(child.dependencySet)
                if child.lemma is None:
                    child.lemma = lemma
                else:
                    try:
                        child.lemma.merge(lemma)
                    except PogException as ex:
                        self.showNode(node)
                        print(str(ex))
                        print("Failed when adding lemma from node %s to child %s" % (str(node), str(child)))
                        sys.exit(1)
        self.addComment("Operations for representing formula")

    def showNode(self, node):
        outs = str(node)
        schildren = [str(c) for c in node.children]
        if len(schildren) > 0:
            outs += " (" + ", ".join(schildren) + ")"
        print(outs)


    def show(self):
        for node in self.nodes:
            if node.ntype in  [NodeType.negation, NodeType.variable]:
                continue
            self.showNode(node)
        print("Root = %s" % str(self.nodes[-1]))
            