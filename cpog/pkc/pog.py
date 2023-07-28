# Quasi-canonical representation of a POG
# For use by top-down POG generators

import sys
import readwrite

class PogException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Pog Exception: " + str(self.value)

# Only represent product and sum nodes
# Variables and Tautology are represented by integer values
class NodeType:
    tcount = 2
    product, sum = range(2)
    typeName = ["product", "sum"]

class Node:
    ntype = None
    xvar = 0
    children = []  # List of literals
    mark = False
    # Added lazily
    dset = None

    def __init__(self, ntype, xvar, children):
        self.xvar = xvar
        self.ntype = ntype
        self.children = children
        self.dset = None

    def string(self, long = True):
        s = 'UNK_' + str(self.xvar)
        if self.ntype == NodeType.product:
            s = 'P_' + str(self.xvar)
        elif self.ntype == NodeType.sum:
            s = 'S_' + str(self.xvar)
        if long and len(self.children) > 0:
            refs = [str(c) for c in self.children]
            s += "(%s)" % ", ".join(refs)
        return s

    def __str__(self):
        return self.string(long = False)

    def findDecisionVariable(self, pog):
        if self.ntype != NodeType.sum:
            return None
        child1 = self.children[0]
        if pog.isNode(child1):
            n1 = pog.getNode(child1)
            lits1 = n1.children
        else:
            lits1 = [child1]
        child2 = self.children[1]
        if pog.isNode(child2):
            n2 = pog.getNode(child2)
            lits2 = n2.children
        else:
            lits2 = [child2]

        for lit1 in lits1:
            for lit2 in lits2:
                if lit1 == -lit2:
                    return abs(lit1)
        return None

    def dependencySet(self, pog):
        if self.dset is not None:
            return self.dset
        else:
            dset = set([])
            for child in self.children:
                if pog.isNode(child):
                    dset = dset | pog.getNode(child).dependencySet(pog)
                else:
                    dset = dset | set([abs(child)])
            self.dset = dset
            return dset

    def __hash__(self):
        return self.xvar

class ProductNode(Node):
    def __init__(self, xvar, children):
        Node.__init__(self, NodeType.product, xvar, children)

class SumNode(Node):
    def __init__(self, xvar, children):
        if len(children) != 2:
            raise PogException("Can't have Sum node with %d children" % len(children))
        Node.__init__(self, NodeType.sum, xvar, children)

def leafPog(variableCount, root):
    pg = Pog(variableCount, 0)
    pg.setRoot(root)
    return pg

# Represent overall POG
class Pog:
    
    inputVariableCount = 0
    variableCount = 0
    # Constant Node literals
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
    rootLiteral = None
    # Node counts by node type
    nodeCounts = {}
    # Number of defining clauses
    definingClauseCount = 0

    def __init__(self, variableCount, verbLevel):
        self.verbLevel = verbLevel
        self.inputVariableCount = variableCount
        self.variableCount = variableCount
        self.nodeMap = {}
        self.nodes = []
        self.varMap = {}
        self.nodeCounts = { t : 0 for t in range(NodeType.tcount) }
        self.definingClauseCount = 0
        # Assume don't need leaves
        self.leaf1 = None
        self.leaf0 = None
        self.rootLiteral = None

    def addLeaves(self):
        if self.leaf1 is not None:
            return
        one = self.findOrMake(NodeType.product, [])
        self.leaf1 = one.xvar
        self.leaf0 = -self.leaf1

    # Create a POG consisting of just a constant or the literal of an input variable
    def leafPog(self, root):
        return leafPog(self.inputVariableCount, root)

    def findOrMake(self, ntype, args):
        args = sorted(args, key=lambda a : abs(a))
        key = tuple([ntype] + args)
        if key in self.nodeMap:
            return self.nodeMap[key]
        self.variableCount += 1        
        xvar = self.variableCount
        if ntype == NodeType.product:
            node = ProductNode(xvar, args) 
        elif ntype == NodeType.sum:
            node = SumNode(xvar, args) 
        self.nodeMap[key] = node
        self.nodes.append(node)
        self.varMap[node.xvar] = node
        self.nodeCounts[ntype] += 1
        self.definingClauseCount += 1 + len(args)
        return node

    def addProduct(self, children):
        nchildren = []
        for child in children:
            if self.leaf0 is not None and child == self.leaf0:
                return child
            elif self.leaf1 is not None and child == self.leaf1:
                continue
            nchildren.append(child)
        if len(nchildren) == 0:
            self.addLeaves()
            return self.leaf1
        elif len(nchildren) == 1:
            return nchildren[0]
        else:
            node = self.findOrMake(NodeType.product, nchildren)
            return node.xvar

    def addSum(self, children):
        nchildren = []
        for child in children:
            if self.leaf1 is not None and child == self.leaf1:
                return child
            elif self.leaf0 is not None and child == self.leaf0:
                continue
            nchildren.append(child)
        if len(nchildren) == 0:
            self.addLeaves()
            return self.leaf0
        elif len(nchildren) == 1:
            return nchildren[0]
        else:
            node = self.findOrMake(NodeType.sum, nchildren)
            return node.xvar

    def setRoot(self, rootLiteral):
        if abs(rootLiteral) == readwrite.tautologyId:
            self.addLeaves()
            rootLiteral = self.leaf1 if rootLiteral > 0 else self.leaf0
        self.rootLiteral = rootLiteral

    def getNode(self, lit):
        var = abs(lit)
        try:
            node = self.varMap[var]
        except:
            raise PogException("Literal %d invalid" % lit)
        return node

    def isNode(self, lit):
        var = abs(lit)
        return var in self.varMap

    def mark(self, lit):
        if not self.isNode(lit):
            return
        node = self.getNode(lit)
        if node.mark:
            return
        node.mark = True
        for c in node.children:
            self.mark(c)

    # Create a new POG consisting of a subgraph with root lit
    def extractSubgraph(self, rootLiteral):
        if not self.isNode(rootLiteral):
            return self.leafPog(rootLiteral)
        # Marking
        for node in self.nodes:
            node.mark = False
        self.mark(rootLiteral)
        # Map from old xvars to new ones
        plits = [v for v in range(1, self.inputVariableCount+1)]
        nlits = [-v for v in plits]
        o2nLit = {lit : lit for lit in plits + nlits}
        npog = Pog(self.inputVariableCount, self.verbLevel)
        for node in self.nodes:
            nnode = None
            if not node.mark:
                continue
            else:
                nchildren = [o2nLit[c] for c in node.children]
                nnode = npog.findOrMake(node.ntype, nchildren)
                o2nLit[node.xvar] = nnode.xvar
                o2nLit[-node.xvar] = -nnode.xvar
        npog.setRoot(o2nLit[rootLiteral])
        return npog

    def compress(self):
        if self.verbLevel >= 3:
            sys.stdout.write("Before compression: ")
            self.summarize()
        npog = self.extractSubgraph(self.rootLiteral)
        self.nodes = npog.nodes
        self.varMap = npog.varMap
        self.nodeMap = npog.nodeMap
        self.nodeCounts = npog.nodeCounts
        self.definingClauseCount = npog.definingClauseCount
        self.rootLiteral = npog.rootLiteral
        if self.verbLevel >= 3:
            sys.stdout.write("After compression: ")
            self.summarize()

    def write(self, fname, numberLines = False):
        pwriter = readwrite.PogWriter(self.inputVariableCount, [], fname, self.verbLevel, numberLines)
        pwriter.doComment("POG nodes")
        for node in self.nodes:
            if node.ntype == NodeType.product:
                pwriter.doProduct(node.xvar, node.children)
            if node.ntype == NodeType.sum:
                pwriter.doSum(node.xvar, node.children)
        if self.rootLiteral is not None:
            pwriter.doRoot(self.rootLiteral)
        pwriter.finish()

    def nodeCount(self):
        return self.nodeCounts[NodeType.product] + self.nodeCounts[NodeType.sum]

    def summarize(self):
        pcount = self.nodeCounts[NodeType.product]
        scount = self.nodeCounts[NodeType.sum]
        ccount = self.definingClauseCount
        print("GEN: POG has %d nodes (%d Product + %d Sum) and %d defining clauses" % (pcount+scount, pcount, scount, ccount))

    # Integrate the nodes of another POG into this one.  Return reference for the remapped root
    def integrate(self, opog):
        if not opog.isNode(opog.rootLiteral):
            return opog.rootLiteral
        # Mapping from old literals to new literals
        plits = [v for v in range(1, self.inputVariableCount+1)]
        nlits = [-v for v in plits]
        remap = {lit : lit for lit in plits + nlits}
        rlit = None
        for onode in opog.nodes:
            oxvar = onode.xvar
            nchildren = [remap[child] for child in onode.children]
            nnode = self.findOrMake(onode.ntype, nchildren)
            nxvar = nnode.xvar
            remap[oxvar] = nxvar
            remap[-oxvar] = -nxvar
        rlit = remap[opog.rootLiteral]
        if self.verbLevel >= 3:
            print("Integration mapped sub-POG root %d to main-POG %d" % (opog.rootLiteral, rlit))
        return rlit


    def show(self):
        for node in self.nodes:
            print(node.string())
        print("Root = %d" % self.rootLiteral)
            
    def showSubgraph(self, lit):
        for node in self.nodes:
            node.mark = False
        self.mark(lit)
        print("Subgraph with root %d:" % lit)
        for node in self.nodes:
            if node.mark:
                print(node.string())
