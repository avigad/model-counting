# Quasi-canonical representation of a POG
# For use by bottom-up POG generators

import sys
import readwrite

class PogException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Pog Exception: " + str(self.value)


class NodeType:
    tcount = 5
    tautology, variable, negation, conjunction, disjunction = range(5)
    typeName = ["taut", "var", "neg", "conjunct", "disjunct"]

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
    # Track original variable of ITE operation
    iteVar = None

    # Id of first clause in defining clauses
    definingClauseId = None
    # Id of clause that validates this as potential root node
    unitClauseId = None
 
    def __init__(self, xlit, ntype, children):
        ProtoNode.__init__(self, ntype, children)
        self.xlit = xlit
        self.iteVar = None
        self.definingClauseId = None
        self.unitClauseId = None

    def name(self):
        if self.xlit < 0:
            return "-P" + str(-self.xlit)
        else:
            return "P" + str(self.xlit)

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

    def __init__(self, children, xlit):
        Node.__init__(self, xlit, NodeType.conjunction, children)
        self.ilist = [child.xlit for child in children]

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
    # Mapping (ntype, arg1, ..., argk) to nodes
    uniqueTable = {}
    # All Nodes
    nodes = []
    # Mapping from xlit to node
    nodeMap = {}
    # Verbosity level
    verbLevel = 1
    cwriter = None
    inputClauseList = []

    # Statistics:
    # Count of each node by type
    nodeCounts = []
    # Total number of defining clauses
    definingClauseCount = 0
    # Added RUP clause counts
    assertedClauseCount = 0
    # Asserted unit clauses
    unitClauseCount = 0

    def __init__(self, variableCount, inputClauseList, fname, verbLevel):
        self.verbLevel = verbLevel
        self.uniqueTable = {}
        self.inputClauseList = readwrite.cleanClauses(inputClauseList)
        self.cwriter = readwrite.CratWriter(variableCount, inputClauseList, fname, verbLevel)
        self.nodeCounts = [0] * NodeType.tcount
        self.definingClauseCount = 0
        self.assertedClauseCount = 0
        self.unitClauseCount = 0

        self.leaf1 = One()
        self.store(self.leaf1)
        self.leaf0 = Negation(self.leaf1)
        self.store(self.leaf0)
        for i in range(1, variableCount+1):
            v = Variable(i)
            self.store(v)
            self.addNegation(v)
        
    def lookup(self, ntype, children):
        n = ProtoNode(ntype, children)
        key = n.key()
        if key in self.uniqueTable:
            return self.uniqueTable[key]
        return None

    # Return node with associated xlit
    def findNode(self, xlit):
        if xlit not in self.nodeMap:
            raise PogException("No node with xlit %d" % xlit)
        return self.nodeMap[xlit]

    def store(self, node):
        key = node.key()
        self.uniqueTable[key] = node
        self.nodeMap[node.xlit] = node

    def remove(self, node):
        key = node.key()
        del self.uniqueTable[key]
        del self.nodeMap[node.xlit]

    def addNegation(self, child):
        if child.ntype == NodeType.negation:
            return child.children[0]
        n = self.lookup(NodeType.negation, [child])
        if n is None:
            n = Negation(child) 
            self.store(n)
        n.definingClauseId = child.definingClauseId
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
            xlit = self.cwriter.newXvar()
            n = Conjunction(children, xlit)
            self.store(n)
            if self.verbLevel >= 2:
                slist = [str(child) for child in n.children]
                self.addComment("Node %s = AND(%s)" % (str(n), ", ".join(slist)))
            ilist = [child.xlit for child in children]
            n.definingClauseId = self.cwriter.finalizeAnd(ilist, xlit)
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
            if self.verbLevel >= 2:
                slist = [str(child) for child in n.children]
                self.addComment("Node %s = OR(%s)" % (str(n), ", ".join(slist)))
            hints = None
            if hintPairs is not None:
                hints = [node.definingClauseId+offset for node,offset in hintPairs]
            ilist = [child.xlit for child in n.children]
            n.definingClauseId = self.cwriter.finalizeOr(ilist, xlit, hints)
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
            ntrue = self.addConjunction([nif, nthen])
            nfalse = self.addConjunction([self.addNegation(nif), nelse])
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
        
            
    def finish(self):
        self.cwriter.finish()
        if self.verbLevel >= 1:
            nnode = 0
            niclause = len(self.inputClauseList)
            ndclause = self.definingClauseCount
            naclause = self.assertedClauseCount
            nuclause = self.unitClauseCount
            nclause = niclause + ndclause + naclause + nuclause
            print("c Nodes by type")
            for t in range(NodeType.tcount):
                if self.nodeCounts[t] == 0:
                    continue
                print("c    %s: %d" % (NodeType.typeName[t], self.nodeCounts[t]))
                nnode += self.nodeCounts[t]
            print("c    TOTAL: %d" % nnode)
            print("c Total defining clauses: %d" % ndclause)
            print("c Asserted clauses for operation justification: %d" % naclause)
            print("c Asserted unit clauses: %d" % nuclause)
            print("Total clauses: %d input + %d defining + %d asserted + %d unit = %d" % (niclause, ndclause, naclause, nuclause, nclause))


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
            
