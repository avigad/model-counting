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
    # Caching of last results
    cacheSize = 5
    # Cache results of unit propagation, using assumptions as key
    # Each entry is tuple of form (key, prop, lits)
    propagateCache = []

    def __init__(self):
        self.solver = Solver(solverId, with_proof = True)
        self.killCache()

    def killCache(self):
        self.propagateCache = []

    def propagate(self, assumptions):
        ta = tuple(assumptions)
        for key,prop,lits in self.propagateCache:
            if ta == key:
                return (prop,lits)
        # Didn't find anything
        prop, lits = self.solver.propagate(ta)
        self.propagateCache.append((ta,prop,lits))
        if len(self.propagateCache) > self.cacheSize:
            self.propagateCache = self.propagateCache[1:]
        return prop, lits

    def addClauses(self, clist):
        self.solver.append_formula(clist)
        self.killCache()

    def rupCheck(self, clause, context, failOK = False):
        assumptions = context + readwrite.invertClause(clause)
        prop, slits = self.propagate(assumptions)
        result = not prop
        return result

    # See if literal among current units
    def isUnit(self, lit, context):
        ok, lits = self.propagate(context)
        val = ok and lit in lits
        return val

    def justifyUnit(self, lit, context):
        clauses =  []
        if self.isUnit(lit, context):
            return clauses
        pclause = readwrite.invertClause(context)
        pclause.append(lit)
        if self.rupCheck(pclause, context, failOK=True):
            clauses.append(pclause)
            self.addClauses([pclause])
            # Sanity check
            if not self.isUnit(lit, context):
                print("WARNING.  Added RUP clause %s, but still don't have unit literal %s in context %s" % (str(pclause), lit, str(context)))
                raise PogException("Proof failure.  Added RUP clause %s, but still don't have unit literal %s in context %s" % (str(pclause), lit, str(context)))
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
        self.addClauses(clauses)
        # Sanity check
        if not self.isUnit(lit, context):
            print("WARNING.  Added SAT clauses %s, but still don't have unit literal %s in context %s" % (str(clauses), lit, str(context)))
            raise PogException("Proof failure.  Added SAT clauses %s, but still don't have unit literal %s in context %s" % (str(clauses), lit, str(context)))
        return clauses
    

class NodeType:
    tcount = 5
    tautology, variable, negation, conjunction, disjunction = range(5)
    typeName = ["taut", "var", "neg", "conjunct", "disjunct"]
    definingClauseCount = [0, 0, 0, 3, 3]

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
    xlit = None
    # Information used during proof generation.  Holdover from when node represented ITE
    iteVar = None
 
    def __init__(self, xlit, ntype, children):
        ProtoNode.__init__(self, ntype, children)
        self.xlit = xlit
        self.iteVar = None
    
    def __hash__(self):
        return self.xlit

    def __str__(self):
        return "%s-%d" % (NodeType.typeName[self.ntype], self.xlit)

    def __eq__(self, other):
        return self.xlit == other.xlit

    def getLit(self):
        return None

class Variable(Node):
    level = 1  # For ordering

    def __init__(self, id):
        Node.__init__(self, id, NodeType.variable, [])

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
    clauseId = None

    def __init__(self, children, xlit, clauseId):
        Node.__init__(self, xlit, NodeType.conjunction, children)
        self.clauseId = clauseId

    def __str__(self):
        return "P%d" % self.xlit

class Disjunction(Node):
    clauseId = None

    def __init__(self, child1, child2, xlit, clauseId):
        Node.__init__(self, xlit, NodeType.disjunction, [child1, child2])
        self.clauseId = clauseId

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
    clauseList = []
    reasoner = None
    # Statistics:
    # Count of each node by type
    nodeCounts = []
    # Traverses of nodes by type
    nodeVisits = []
    # Added RUP clause counts, indexed by number of clauses to justify single literal
    literalClauseCounts = {}
    # Added RUP clause counts, indexed by node type
    nodeClauseCounts = []

    def __init__(self, variableCount, clauseList, fname, verbLevel = 1):
        self.verbLevel = verbLevel
        self.uniqueTable = {}
        self.clauseList = clauseList
        self.cwriter = readwrite.CratWriter(variableCount, clauseList, fname, verbLevel)
        self.reasoner = Reasoner()
        self.reasoner.addClauses(clauseList)
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
        children = sorted(nchildren, key = lambda c: abs(c.xlit))
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
                return node.clauseId+idx+1
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

    # hlist members can be clauseId or (node, offset), where 0 <= offset < 3
    def addClause(self, nodes, hlist = None):
        lits = [n.xlit for n in nodes]
        if hlist is None:
            hints = ['*']
        else:
            hints = []
            for h in hlist:
                if type(h) == type((1,2)):
                    hint = h[0].clauseId = h[1]
                else:
                    hint = h
                hints.append(hint)
        self.cwriter.doClause(lits, hints)

    def addComment(self, s):
        self.cwriter.doComment(s)

    def deleteClause(self, id, hlist = None):
        self.cwriter.doDeleteClause(id, hlist)

    def deleteOperation(self, node):
        self.cwriter.doDeleteOperation(node.xlit, node.clauseId)
        
    def validateDisjunction(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        extraUnits = []
        if root.iteVar is None:
            raise PogException("Don't know how to validate OR node %s that is not from ITE" % str(root))
        svar = root.iteVar
        # Recursively validate children
        extraUnits += self.validateUp(root.children[0], context + [svar], root)
        extraUnits += self.validateUp(root.children[1], context + [-svar], root)
        # Assert extension literal.  Requires two steps to get both sides of disjunction
        if self.verbLevel >= 2:
            self.addComment("Assert ITE at node %s%s" % (str(root), rstring))
        icontext = readwrite.invertClause(context)
        clause = [root.iteVar, root.xlit] + icontext
        self.cwriter.doClause(clause)
        clause = clause[1:]
        cid = self.cwriter.doClause(clause)
        self.nodeClauseCounts[root.ntype] += 2
        if parent is not None and len(context) == 0:
            extraUnits.append(cid)
        return extraUnits

    def validateConjunction(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        extraUnits = []
        vcount = 0
        for c in root.children:
            clit = c.getLit()
            if clit is None:
                extraUnits += self.validateUp(c, context, root)
                vcount += 1
            else:
                clauses = self.reasoner.justifyUnit(clit, context)
                if len(clauses) == 0:
                    if self.verbLevel >= 3:
                        print("Found unit literal %d in context %s" % (clit, str(context)))
                elif self.verbLevel >= 2:
                    self.addComment("Justify literal %d in context %s " % (clit, str(context)))
                    if self.verbLevel >= 3:
                        print("Justified unit literal %d in context %s with %d proof steps" % (clit, str(context), len(clauses)))
                for clause in clauses:
                    self.cwriter.doClause(clause)
                nc = len(clauses)
                if nc in self.literalClauseCounts:
                    self.literalClauseCounts[nc] += 1
                else:
                    self.literalClauseCounts[nc] = 1
        if vcount > 1:
            # Assert extension literal
            if self.verbLevel >= 2:
                self.addComment("Assert unit clause for AND node %s%s" % (str(root), rstring))
            clause = [root.xlit] + readwrite.invertClause(context)
            cid = self.cwriter.doClause(clause)
            self.nodeClauseCounts[root.ntype] += 1
            if parent is not None and len(context) == 0:
                extraUnits.append(cid)
        return extraUnits

    def validateOther(self, root, context, parent):
        rstring = " (root)" if parent is None else ""
        extraUnits = []
        if root.iteVar is not None:
            # This node was generated from an ITE.
            if self.verbLevel >= 2:
                self.addComment("Assert clause for root of ITE %s" % rstring)
            clause = [root.xlit] + readwrite.invertClause(context)
            cid = self.cwriter.doClause(clause)
            self.nodeClauseCounts[root.ntype] += 1
            if parent is not None and len(context) == 0:
                extraUnits.append(cid)
        else:
            raise PogException("Don't know how to validate node %s" % str(root))
        return extraUnits

    # Generate justification of root nodes
    # context is list of literals that are assigned in the current context
    # Returns list of unit clauses that should be deleted
    def validateUp(self, root, context, parent = None):
        self.nodeVisits[root.ntype] += 1
        if root.ntype == NodeType.disjunction:
            return self.validateDisjunction(root, context, parent)
        elif root.ntype == NodeType.conjunction:
            return self.validateConjunction(root, context, parent)
        else:
            return self.validateOther(root, context, parent)

                
    def doValidate(self):
        root = self.nodes[-1]
        extraUnits = self.validateUp(root, [], parent = None)
        if self.verbLevel >= 1 and len(extraUnits) > 0:
            self.addComment("Delete extra unit clauses")
        for cid in extraUnits:
            self.deleteClause(cid)
        if self.verbLevel >= 1:
            self.addComment("Delete input clauses")
        for cid in range(1, len(self.clauseList)+1):
            self.deleteClause(cid)
            
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
            niclause = len(self.clauseList)
            nclause = niclause + ndclause + nlclause + nnclause
            print("Total clauses: %d input + %d defining + %d literal justification + %d node justifications = %d" % (niclause, ndclause, nlclause, nnclause, nclause))

    def doMark(self, root, markSet):
        if root.xlit in markSet:
            return
        markSet.add(root.xlit)
        for c in root.children:
            self.doMark(c, markSet)
        

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
            
        
        
