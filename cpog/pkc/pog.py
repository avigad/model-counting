# Quasi-canonical representation of a POG
# For use by top-down POG generators

import sys
import readwrite

class PogException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Pog Exception: " + str(self.value)

class NodeType:
    tcount = 4
    tautology, variable, product, sum = range(4)
    typeName = ["taut", "var", "product", "sum"]


class NodeRef:
    node = None
    phase = True
    def __init__(self, node, phase):
        self.node = node
        self.phase = phase

    def literal(self):
        weight = 1 if self.phase else -1
        return self.node.xvar * weight

    def negate(self):
        return NodeRef(self.node, not self.phase)

    def __str__(self):
        return str(self.node) if self.phase else '!' + str(self.node)

class Node:
    ntype = None
    xvar = 0
    children = []  # List of node references
    mark = False

    def __init__(self, ntype, xvar, children):
        self.xvar = xvar
        self.ntype = ntype
        self.children = children

    def __str__(self):
        if self.ntype == NodeType.tautology:
            return "TAUT"
        elif self.ntype == NodeType.variable:
            return 'V' + str(self.xvar)
        elif self.ntype == NodeType.product:
            return 'P_' + str(self.xvar)
        elif self.ntype == NodeType.sum:
            return 'S_' + str(self.xvar)
        else:
            return 'UNK_' + str(self.xvar)

    def show(self):
        s = str(self)
        if len(self.children) > 0:
            refs = [str(c.literal()) for c in self.children]
            s += "(%s)" % ", ".join(refs)
        print(s)

    def findSplittingLiteral(self):
        if self.ntype != NodeType.sum:
            return None
        child1 = self.children[0]
        n1, p1 = child1.node, child1.phase
        if n1.ntype == NodeType.variable:
            lits1 = [child1.literal()]
        elif n1.ntype  == NodeType.product and p1:
            lits1 = [c.literal() for c in n1.children]
        else:
            return None

        child2 = self.children[1]
        n2, p2 = child2.node, child2.phase
        if n2.ntype == NodeType.variable:
            lits2 = [child2.literal()]
        elif n2.ntype  == NodeType.product and p2:
            lits2 = [c.literal() for c in n2.children]
        else:
            return None

        for lit1 in lits1:
            for lit2 in lits2:
                if lit1 == -lit2:
                    return lit1
        return None


class Tautology(Node):

    def __init__(self):
        Node.__init__(self, NodeType.tautology, readwrite.tautologyId, [])
        
class Variable(Node):
    def __init__(self, id):
        Node.__init__(self, NodeType.variable, id, [])


class ProductNode(Node):
    def __init__(self, xvar, children):
        Node.__init__(self, NodeType.product, xvar, children)

class SumNode(Node):
    def __init__(self, xvar, children):
        if len(children) != 2:
            raise PogException("Can't have Sum node with %d children" % len(children))
        Node.__init__(self, NodeType.sum, xvar, children)

# Represent overall POG
class Pog:
    
    inputVariableCount = 0
    variableCount = 0
    # Constant Node references
    leaf1 = None
    leaf0 = None
    # map from type + args to node
    nodeMap = {}
    # All Nodes
    nodes = []
    # Mapping from variable to node
    varMap = {}
    # Verbosity level
    verbLevel = 1
    inputClauseList = []
    rootLiteral = None
    # Node counts by node type
    nodeCounts = {}
    # Number of defining clauses
    definingClauseCount = 0

    def __init__(self, variableCount, inputClauseList, verbLevel):
        self.verbLevel = verbLevel
        self.inputVariableCount = variableCount
        self.variableCount = variableCount
        self.inputClauseList = readwrite.cleanClauses(inputClauseList)
        self.nodeMap = {}
        self.nodes = []
        self.varMap = {}
        self.nodeCounts = { t : 0 for t in range(NodeType.tcount) }
        self.definingClauseCount = 0
        one = self.findOrMake(NodeType.tautology)
        self.leaf1 = NodeRef(one, True)
        self.leaf0 = NodeRef(one, False)
        for i in range(1, variableCount+1):
            v = self.findOrMake(NodeType.variable, i)
        self.rootLiteral = None

    def buildKey(self, ntype, xvar = None, args = None):
        key = [ntype]
        if xvar is not None:
            key.append(xvar)
        if args is not None:
            key = key + [arg.literal() for arg in args]
        return tuple(key)

    def nodeKey(self, node):
        ntype = node.ntype
        xvar = None if ntype == NodeType.tautology else node.xvar
        args = None if ntype in [NodeType.tautology, NodeType.variable] else node.children
        return self.buildKey(ntype, xvar, args)

    def findOrMake(self, ntype, xvar = None, args = None):
        if args is not None:
            args.sort(key=lambda r : r.node.xvar)
        key = self.buildKey(ntype, xvar, args)
        if key in self.nodeMap:
            return self.nodeMap[key]
        if ntype == NodeType.tautology:
            node = Tautology()
        elif ntype == NodeType.variable:
            node = Variable(xvar)
        elif ntype == NodeType.product:
            self.variableCount += 1
            xvar = self.variableCount
            node = ProductNode(xvar, args) 
        elif ntype == NodeType.sum:
            self.variableCount += 1
            xvar = self.variableCount
            node = SumNode(xvar, args) 
        self.nodeMap[key] = node
        self.nodes.append(node)
        self.varMap[node.xvar] = node
        self.nodeCounts[ntype] += 1
        if ntype in [NodeType.product, NodeType.sum]:
            self.definingClauseCount += 1 + len(args)
        return node

    def addProduct(self, children):
        nchildren = []
        for child in children:
            node, phase = child.node, child.phase
            if node.ntype == NodeType.tautology:
                if phase:
                    continue
                else:
                    return self.leaf0
            else:
                nchildren.append(child)
        if len(nchildren) == 0:
            return self.leaf1
        elif len(nchildren) == 1:
            return nchildren[0]
        else:
            node = self.findOrMake(NodeType.product, args = nchildren)
            return NodeRef(node, True)

    def addSum(self, children):
        nchildren = []
        for child in children:
            node, phase = child.node, child.phase
            if node.ntype == NodeType.tautology:
                if phase:
                    return self.leaf1
                else:
                    continue
            else:
                nchildren.append(child)
        if len(nchildren) == 0:
            return self.leaf0
        elif len(nchildren) == 1:
            return nchildren[0]
        else:
            node = self.findOrMake(NodeType.sum, args = nchildren)
            return NodeRef(node, True)

    def setRoot(self, rootLiteral):
        self.rootLiteral = rootLiteral
      

    def getRef(self, lit):
        var = abs(lit)
        try:
            node = self.varMap[var]
        except:
            raise PogException("Literal %d invalid" % lit)
        phase = lit > 0
        return NodeRef(node, phase)

    def isNode(self, lit):
        ref = self.getRef(lit)
        return ref.node.ntype in [NodeType.product, NodeType.sum]

    def mark(self, lit):
        node = self.getRef(lit).node
        if node.mark:
            return
        node.mark = True
        for c in node.children:
            self.mark(c.literal())

    def compress(self):
        # Marking
        for node in self.nodes:
            node.mark = False
        self.mark(self.rootLiteral)
        nnodes = []
        nvarMap = {}
        nnodeMap = {}
        nnodeCounts = { t : 0 for t in range(NodeType.tcount) }

        for node in self.nodes:
            if not node.mark and node.ntype in [NodeType.product, NodeType.sum]:
                continue
            nnodes.append(node)
            nvarMap[node.xvar] = node
            key = self.nodeKey(node)
            nnodeMap[key] = node
            nnodeCounts[node.ntype] += 1
        self.nodes = nnodes
        self.varMap = nvarMap
        self.nodeMap = nnodeMap
        self.nodeCounts = nnodeCounts
        

    def write(self, fname):
        pwriter = readwrite.PogWriter(self.inputVariableCount, self.inputClauseList, fname, self.verbLevel)
        pwriter.doComment("POG nodes")
        for node in self.nodes:
            if node.ntype == NodeType.product:
                pwriter.doProduct(node.xvar, [c.literal() for c in node.children])
            if node.ntype == NodeType.sum:
                pwriter.doSum(node.xvar, [c.literal() for c in node.children])
        if self.rootLiteral is not None:
            pwriter.doRoot(self.rootLiteral)
        pwriter.finish()


    def summarize(self):
        pcount = self.nodeCounts[NodeType.product]
        scount = self.nodeCounts[NodeType.sum]
        ccount = self.definingClauseCount
        print("GEN: POG has %d nodes (%d Product + %d Sum) and %d defining clauses" % (pcount+scount, pcount, scount, ccount))

    def show(self):
        for node in self.nodes:
            if node.ntype in  [NodeType.tautology, NodeType.variable]:
                continue
            node.show()
        print("Root = %d" % self.rootLiteral)
            
