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


# Convert DNNF representation of Boolean formula into a POG

import readwrite
import pog

### Standard .ddnnf format

# Format documentation: http://www.cril.univ-artois.fr/kc/d-DNNF-reasoner.html
# Standard Input/output format:
# A d-DNNF representation is encoded using the format used by the c2d
# compiler. According to the compiler language specification, a d-DNNF
# representation is encoded as follows:
# 
# First, a preamble line nnf v e n where
#         v is the number of nodes,
#         e is the number of edges,
#         n is the number of Boolean variables under consideration;
# 
# Then, a sequence of leaf-nodes (one per line), and-nodes and or-nodes,
# appearing according to the topological order (children must be
# described before their parents); note that every node is implicitly
# indexed by an integer from 0 to v-1, such that the induced order
# respects the order of declaration.
# 
# A leaf node is specified by an expression L [-]j, where j (resp. -j)
# denotes the positive (resp. negative) literal of the j th variable
# (with j in [1,...,n]). One can build Boolean constant nodes using
# special cases of and-nodes and or-nodes (defined below): A 0 stands
# for true, while O 0 0 stands for false.
# 
# An and-node is declared using a statement A c i1 ... ic where c is the
# number of children the and-node admits, and i1 ... ic are the indexes
# of these children. An or-node is declared using a statement O j c i1
# ... ic where c i1 ... ic give the node children and j defines the
# variable on which the children conflicts if it is different from
# 0. Note that as we consider d-DNNF representations, the two following
# patterns are the only ones which are allowed:
# 
#     O j 2 i1 i2 for a decision node,
#     O 0 0 for the false node.

### D4's .ddnnf format

# https://github.com/crillab/d4/blob/main/README.md
#
# To get the resulting decision-DNNF representation in file /tmp/test.nnf please use:
# 
# ./d4 -dDNNF benchTest/littleTest.cnf -out=/tmp/test.nnf
# cat /tmp/test.nnf
# o 1 0
# o 2 0
# o 3 0
# t 4 0
# 3 4 -2 3 0
# 3 4 2 0
# 2 3 -1 0
# 2 4 1 0
# 1 2 0
#
# Note that the format used now is an extension of the previous format
# (as defined in the archive of c2d available from
# http://reasoning.cs.ucla.edu/c2d/). The management of propagated
# literals has been improved in the new format, where both nodes and
# arcs are represented. When a literal becomes true at some node there
# is no more need to create an AND node and a literal node to capture it.
# Instead the literal is attached to the arc connecting the
# node with its father. Each line represents a node or an arc, and is
# terminated by 0. When a line represents a node it starts with a
# node type and is followed by its index. Here are the node types:
# 
# o, for an OR node
# f, for a false leaf
# t, for a true leaf
# a, for an AND node (not present in this example)
# 
# The second argument just after the type of node is its index.
# 
# In the example above the decision-DNNF representation has
# 3 OR nodes (1, 2 and 3) and 1 true node (4).
# 
# As expected arcs are used to connect the nodes. In the file .nnf,
# arcs are represented by lines starting with a node index (a positive
# integer, the source node), followed by another node index (a
# positive integer, the target node), and eventually a sequence of literals
# that represents the unit literals that become true at the target node.
#
# In the example, 3 4 -2 3 0 means that OR node of index 3 is connected to the
# true node of index 4 and the literals -2 and 3 are set to true.

class NnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Nnf Exception: " + str(self.value)

class NodeType:
    conjunction, disjunction, leaf, constant = range(4)
    symbol = ['A', 'O', 'L', 'K', 'ITE']
    
    def name(ntype):
        if ntype < 0 or ntype >= 4:
            return "T%d" % ntype
        return NodeType.symbol[ntype]

class Node:
    ntype = None
    id = None
    children = []
    # Corresponding POG Ref
    pref = None

    def __init__(self, ntype, id, children):
        self.ntype = ntype
        self.id = id
        self.children = children
        self.pref = None
        
    def cstring(self):
        slist = ["N%d" % c.id for c in self.children]
        return '(' + ", ".join(slist) + ')'

    def __str__(self):
        return "N%d:%s%s" % (self.id, NodeType.name(self.ntype), self.cstring())

    def show(self):
        print(str(self))

class AndNode(Node):
    
    def __init__(self, id, children):
        # Put literal children before others
        lchildren = []
        nchildren = []
        for c in children:
            if c.ntype == NodeType.leaf:
                lchildren.append(c)
            else:
                nchildren.append(c)
        Node.__init__(self, NodeType.conjunction, id, lchildren + nchildren)
        

# Attempt optimizations
def optAndNode(id, children):
    # Get rid of constant children
    nchildren = []
    for child in children:
        if child.ntype == NodeType.constant:
            if child.val == 0:
                nchildren = [child]
                break
        else:
            nchildren.append(child)
    # Look for simplifications
    if len(nchildren) == 0:
        result = ConstantNode(id, 1)
    elif len(nchildren) == 1:
        result = nchildren[0]
    else:
        result = AndNode(id, nchildren)
    return result

class OrNode(Node):

    def __init__(self, id, children):
        Node.__init__(self, NodeType.disjunction, id, children)

def optOrNode(id, children):
    nchildren = []
    for child in children:
        if child.ntype == NodeType.constant:
            if child.val == 1:
                nchildren = [child]
                break
        else:
            nchildren.append(child)
    if len(nchildren) == 0:
        return ConstantNode(id, 0)
    if len(nchildren) == 1:
        return nchildren[0]
    return OrNode(id, nchildren)

class LeafNode(Node):
    
    lit = None
    def __init__(self, id, lit):
        Node.__init__(self, NodeType.leaf, id, [])
        self.lit = lit

    def cstring(self):
        return '(' + str(self.lit) + ')'

class ConstantNode(Node):

    val = None
    def __init__(self, id, val):
        Node.__init__(self, NodeType.constant, id, [])
        self.val = val

    def cstring(self):
        return str(self.val)

class Nnf:
    verbLevel = 1
    inputCount = 0
    # Nodes are topologically ordered but their ids don't necessarily
    # match position in the array, nor are they necessarily in
    # ascending order
    nodes = []

    def __init__(self, verbLevel):
        self.inputCount = 0
        self.nodes = []
        self.verbLevel = verbLevel

    def nodeCount(self):
        count = 0
        return len(self.nodes)

    def read(self, infile):
        lineNumber = 0
        gotHeader = False
        ncount = 0
        ecount = 0
        # Mapping from node id (given by order in file) to node
        # Optimizations may cause some nodes to be reused
        # but will maintain topological order
        nodeDict = {}
        for line in infile:
            line = readwrite.trim(line)
            lineNumber += 1
            fields = line.split()
            if len(fields) == 0:
                continue
            elif fields[0][0] == 'c':
                continue
            elif not gotHeader and fields[0] == 'nnf':
                gotHeader = True
                try:
                    ncount, ecount, self.inputCount = [int(f) for f in fields[1:]]
                except:
                    print("ERROR:Line #%d (%s).  Invalid header" % (lineNumber, line))
                    return False
            elif not gotHeader:
                print("ERROR:Line #%d.  No header found" % (lineNumber))
            elif fields[0] == 'L':
                lit = 0
                if len(fields) != 2:
                    print("ERROR:Line #%d (%s).  Literal declaration should contain one argument" % (lineNumber, line))
                    return False
                try:
                    lit = int(fields[1])
                except:
                    print("ERROR:Line #%d (%s).  Invalid literal" % (lineNumber, line))
                    return False
                var = abs(lit)
                if var < 1 or var > self.inputCount:
                    print("ERROR:Line #%d (%s).  Out of range literal" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = LeafNode(id, lit)
                nodeDict[id] = nnode
            elif fields[0] == 'A':
                try:
                    vals = [int(f) for f in fields[1:]]
                except:
                    print("ERROR:Line #%d (%s).  Nonnumeric argument" % (lineNumber, line))
                    return False
                if len(vals) == 0 or vals[0] != len(vals)-1:
                    print("ERROR:Line #%d (%s).  Incorrect number of arguments" % (lineNumber, line))
                    return False
                try:
                    children = [nodeDict[i] for i in vals[1:]]
                except:
                    print("ERROR:Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = optAndNode(id, children)
                nodeDict[id] = nnode
            elif fields[0] == 'O':
                try:
                    vals = [int(f) for f in fields[1:]]
                except:
                    print("ERROR:Line #%d (%s).  Nonnumeric argument" % (lineNumber, line))
                    return False
                if len(vals) < 2 or vals[1] != len(vals)-2:
                    print("ERROR:Line #%d (%s).  Incorrect number of arguments (%d)" % (lineNumber, line, len(vals)))
                    return False
                nnode = None
                splitVar = vals[0]  # Ignored
                try:
                    children = [nodeDict[i] for i in vals[2:]]
                except:
                    print("ERROR:Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = optOrNode(id, children)
                nodeDict[id] = nnode
        if not gotHeader:
            print("ERROR:No header found")
            return False
        # Compress into list
        self.nodes = []
        for id in sorted(nodeDict.keys()):
            node = nodeDict[id]
            if id == node.id:
                self.nodes.append(node)
            else:
                key = node.key()
                del self.uniqueTable[key]
        root = nodeDict[len(nodeDict)-1]
        self.topoSort(root)
        return True

    # Perform topological sort of nodes, with root at end
    # Eliminating any unreachable nodes
    def topoSort(self, root):
        nodeList = []
        markSet = set([])
        self.topoTraverse(root, nodeList, markSet)
        self.nodes = nodeList
        if self.verbLevel >= 3:
            print("Topological sort:")
            self.show()
        
    # Traverse nodes for topological sorting
    def topoTraverse(self, root, nodeList, markSet):
        if root.id in markSet:
            return
        markSet.add(root.id)
        for c in root.children:
            self.topoTraverse(c, nodeList, markSet)
        nodeList.append(root)

    def show(self):
        for n in self.nodes:
            n.show()

    def makePog(self, clauseList):
        pg = pog.Pog(self.inputCount, clauseList, self.verbLevel)
        for node in self.nodes:
            pchildren = [child.pref for child in node.children]
            if node.ntype == NodeType.constant:
                node.pref = pg.leaf1 if node.val == 1 else pg.leaf0
            elif node.ntype == NodeType.leaf:
                node.pref = pg.getRef(node.lit)
            elif node.ntype == NodeType.conjunction:
                node.pref = pg.addProduct(pchildren)
            elif node.ntype == NodeType.disjunction:
                node.pref = pg.addSum(pchildren)
            if self.verbLevel >= 3:
                print("NNF node %s --> POG node %s" % (str(node), str(node.pref)))
        pg.setRoot(self.nodes[-1].pref.literal())
        return pg
                
# Read NNF file in format generated by d4
class D4Reader:
    # Underlying NNF
    nnf = None
    # Dictionary of node prototypes, indexed by prototype ID (pid)
    # Each is tuple of form (symbol, pchildren)
    # Each pchild is tuple (other, literals), where literals is set of literals 
    # that are conjoined as guard
    prototypes = {}
    # Mapping from operator IDs in file to Ids in network
    pidMap = {}

    def __init__(self, nnf):
        self.nnf = nnf
        self.prototypes = {}
        self.pidMap = {}

    def showPrototype(self):
        pidList = sorted(self.prototypes.keys())
        for pid in pidList:
            symbol, pchildren = self.prototypes[pid]
            print("Prototype operation %d.  Symbol=%s" % (pid, symbol))
            for other, lits in pchildren:
                print("   Lits=%s, other=%d" % (str(lits), other))


    def read(self, infile):
        lineNumber = 0
        for line in infile:
            line = readwrite.trim(line)
            lineNumber += 1
            fields = line.split()
            if len(fields) == 0:
                continue
            if (fields[-1]) != '0':
                print("Line #%d.  Invalid.  Must terminate with '0'" % lineNumber)
                return False
            fields = fields[:-1]
            if len(fields) < 2:
                print("Line #%d.  Invalid.  Not enough fields" % lineNumber)
                return False
            symbol = fields[0][0] if len(fields[0]) == 1 and fields[0][0] in 'aotf' else None
            if symbol is not None:
                fields = fields[1:]
            try:
                ifields = [int(f) for f in fields]
            except:
                print("Line #%d.  Expected integer argument" % lineNumber)
                return False
            if symbol is None:
                parent = ifields[0]
                pchild = ifields[1]
                lits = ifields[2:]
                if len(lits) > 0:
                    self.nnf.inputCount = max(self.nnf.inputCount, max([abs(lit) for lit in lits]))
                if parent not in self.prototypes or pchild not in self.prototypes:
                    print("Line %d.  Unknown operator ID")
                    return False
                tup = (pchild, lits)
                self.prototypes[parent][1].append(tup)
            else:
                id = ifields[0]
                if id in self.prototypes:
                    print("Line #%d.  Duplicate node declaration" % lineNumber)
                    return False
                self.prototypes[id] = (symbol, [])
        if self.nnf.verbLevel >= 3:
            self.showPrototype()
        return True

    # Position constant and literal nodes with easily determined operator IDs

    def getConstantId(self, val):
        return val

    def getLiteralId(self, lit):
        if lit > 0:
            return 2*lit
        else:
            return 2*(-lit) + 1

    def translateLiterals(self, lits):
        return [self.nnf.nodes[self.getLiteralId(lit)] for lit in lits]

    # Create base components of NNF
    # Put constant nodes first
    # Then add literals
    def buildBase(self):
        # Create constant nodes
        for val in range(2):
            id = self.getConstantId(val)
            self.nnf.nodes.append(ConstantNode(id, val))
        # Create nodes for all input literals
        for v in range(1, self.nnf.inputCount+1):
            posid = self.getLiteralId(v)
            self.nnf.nodes.append(LeafNode(posid, v))
            negid = self.getLiteralId(-v)
            self.nnf.nodes.append(LeafNode(negid, -v))
        if self.nnf.verbLevel >= 3:
            print("Base nodes:")
            for idx in range(len(self.nnf.nodes)):
                print("  NNF node #%d: %s" % (idx, str(self.nnf.nodes[idx])))

    def processFalse(self, pid, pchildren):
        id = self.getConstantId(0)
        self.pidMap[pid] = self.nnf.nodes[id]
        return True

    def processTrue(self, pid, pchildren):
        id = self.getConstantId(1)
        self.pidMap[pid] = self.nnf.nodes[id]
        return True

    # Edge consists of list of literals plus operator.
    # Translate into list of operations
    def processEdge(self, pchild):
        cpid, lits = pchild
        children = self.translateLiterals(lits)
        children.append(self.pidMap[cpid])
        return children

    # Tentatively create new operator for disjunction
    # But may simplify to existing operator
    def doDisjunction(self, args):
        nextId = len(self.nnf.nodes)+1
        arg = optOrNode(nextId, args)
        if arg.id == nextId:
            self.nnf.nodes.append(arg)
        return arg

    # Tentatively create new operator for conjunction
    # But may simplify to existing operator
    def doConjunction(self, args):
        nextId = len(self.nnf.nodes)+1
        arg = optAndNode(nextId, args)
        if arg.id == nextId:
            self.nnf.nodes.append(arg)
        return arg

    def processOr(self, pid, pchildren):
        achildren = []
        for pchild in pchildren:
            children = self.processEdge(pchild)
            arg = self.doConjunction(children)
            achildren.append(arg)
        if len(achildren) == 1:
            self.pidMap[pid] = achildren[0]
        elif len(achildren) == 2:
            op = self.doDisjunction(achildren)
            self.pidMap[pid] = op
        else:
            print("Or Operation #%d.  Can't have operation with %d arguments" % (pid, len(achildren)))
            return False
        if self.nnf.verbLevel >= 4:
            print("Processed Or operation #%d.  Result = POG operation %s" % (pid, str(self.pidMap[pid])))
        return True

    def processAnd(self, pid, pchildren):
        achildren = []
        for pchild in pchildren:
            children = self.processEdge(pchild)
            achildren += children
        op = self.doConjunction(achildren)
        self.pidMap[pid] = op
        return True

    # Add one more node.
    # Most, but not all are in topological order
    def buildNode(self, pid):
        if pid in self.pidMap:
            return True
        ok = True
        symbol, pchildren = self.prototypes[pid]
        for pchild in pchildren:
            cpid, lits = pchild
            if not self.buildNode(cpid):
                return False
        if symbol == 't':
            ok = self.processTrue(pid, pchildren)
        elif symbol == 'f':
            ok = self.processFalse(pid, pchildren)
        elif symbol == 'o':
            ok = self.processOr(pid, pchildren)
        else:
            # 'a'
            ok = self.processAnd(pid, pchildren)
        if not ok:
            print("Operation #%d.  Generation of NNF graph failed." % pid)
            return False
        if self.nnf.verbLevel >= 4:
            print("Processed operation #%d.  Symbol=%s" % (pid, symbol))
        return True

    def build(self):
        self.buildBase()
        pidList = sorted(self.prototypes.keys())
        pidList.reverse()
        for pid in pidList:
            if not self.buildNode(pid):
                return False
        return True
