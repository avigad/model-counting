# Quasi-canonical representation of a counting schema
# For use by both top-down and bottom-up schema generators

from functools import total_ordering

import sys
import writer
import logic


class SchemaException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Schema Exception: " + str(self.value)


class NodeType:
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
 
    def __init__(self, xlit, ntype, children):
        ProtoNode.__init__(self, ntype, children)
        self.xlit = xlit
    
    def __hash__(self):
        return self.xlit

    def __str__(self):
        return "%s-%d" % (NodeType.typeName[self.ntype], self.xlit)

    def __eq__(self, other):
        return self.xlit == other.xlit

    def key(self):
        return tuple([self.ntype] + [child.xlit for child in self.children])

@total_ordering
class Variable(Node):
    level = 1  # For ordering

    def __init__(self, id, level=None):
        Node.__init__(self, id, NodeType.variable, [])
        self.level = id if level is None else level

    def __ne__(self, other):
        return self.level != other.level

    def __lt__(self, other):
        return self.level < other.level

    def key(self):
        return (self.ntype, self.xlit)

    def __str__(self):
        return "V" + str(self.xlit)

class One(Node):
    def __init__(self):
        Node.__init__(self, logic.tautologyId, NodeType.tautology, [])

    def __str__(self):
        return "TAUT"


class Negation(Node):
    
    def __init__(self, child):
        Node.__init__(self, -child.xlit, NodeType.negation, [child])

    def __str__(self):
        return "!" + str(self.children[0])

class Conjunction(Node):
    clauseId = None

    def __init__(self, child1, child2, xlit, clauseId):
        Node.__init__(self, xlit, NodeType.conjunction, [child1, child2])
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

# Represent overall schema
class Schema:
    
    # List of variables, ordered by level
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
    
    def __init__(self, variableCount, clauseList, froot, variableOrder = None, verbLevel = 1):
        self.verbLevel = verbLevel
        self.uniqueTable = {}
        self.cwriter = writer.CratWriter(variableCount, clauseList, froot, verbLevel)
        self.leaf1 = One()
        self.store(self.leaf1)
        self.leaf0 = Negation(self.leaf1)
        self.store(self.leaf0)
        self.variables = []
        for i in range(1, variableCount+1):
            self.addVariable(i)
        if variableOrder is not None:
            for level in range(1, variableCount+1):
                id = variableOrder[level-1]
                self.variables[id-1].level = level

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
#        print("UniqueTable[%s] = %s" % (str(key), str(node)))
        self.nodes.append(node)

    def addVariable(self, id):
        v = Variable(id)
        self.variables.append(v)
        self.store(v)

    def addNegation(self, child):
        if child.ntype == NodeType.negation:
            return child.children[0]
        n = self.lookup(NodeType.negation, [child])
        if n is None:
            n = Negation(child)
            self.store(n)
        return n

    def addConjunction(self, child1, child2):
        if child1.isZero() or child2.isZero():
            return self.leaf0
        if child1.isOne():
            return child2
        if child2.isOne():
            return child1
        n = self.lookup(NodeType.conjunction, [child1, child2])
        if n is None:
            xlit, clauseId = self.cwriter.doAnd(child1.xlit, child2.xlit)
            n = Conjunction(child1, child2, xlit, clauseId)
            self.store(n)
        return n

    def addDisjunction(self, child1, child2, hints = ['*']):
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
            self.store(n)
        return n

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
        elif (nthen.ntype == NodeType.negation or nthen.isConstant()) and (nelse.ntype == NodeType.negation or nelse.isConstant()):
            result = self.addNegation(self.addIte(nif, self.addNegation(nthen), self.addNegation(nelse)))
        elif nthen.isOne():
            result = self.addNegation(self.addConjunction(self.addNegation(nif), self.addNegation(nelse)))
        elif nthen.isZero():
            result = self.addConjunction(self.addNegation(nif), nelse)
        elif nelse.isOne():
            result = self.addNegation(self.addConjunction(nif, self.addNegation(nthen)))
        elif nelse.isZero():
            result = self.addConjunction(nif, nthen)
        else:
            ntrue = self.addConjunction(nif, nthen)
            nfalse = self.addConjunction(self.addNegation(nif), nelse)
            hints = [ntrue.clauseId+1, nfalse.clauseId+1]
            n = self.addDisjunction(ntrue, nelse, hints)
            result = n
#        print("ITE(%s, %s, %s) --> %s" % (str(nif), str(nthen), str(nelse), str(result)))
        return result

    # hlist can be clauseId or (node, offset), where 0 <= offset < 3
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

    def deleteClause(self, id):
        self.cwriter.doDeleteClause(id)

    def deleteOperation(self, node):
        self.cwriter.doDeleteOperation(node.xlit, node.clauseId)
        
        
        
        
