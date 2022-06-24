#!/usr/bin/python3

# Convert DNNF representation of Boolean formula into a counting schema

import sys
import getopt
import readwrite
import schema

# Format documentation: http://www.cril.univ-artois.fr/kc/d-DNNF-reasoner.html
# Input/output format:


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



def usage(name):
    print("Usage: %s [-h] [-v] [-i FILE.cnf] [-n FILE.nnf] [-p FILE.crat]")
    print(" -h           Print this message")
    print(" -v           Add comments to files")
    print(" -i FILE.cnf  Input CNF")
    print(" -n FILE.nnf  Input NNF")
    print(" -p FILE.crat Output CRAT")

def trim(line):
    while len(line) > 0 and line[-1] == '\n':
        line = line[:-1]
    return line

class NodeType:
    conjunction, disjunction, leaf, constant, ite = range(5)
    symbol = ['A', 'O', 'L', 'K', 'ITE']
    
    def name(ntype):
        if ntype < 0 or ntype >= 5:
            return "T%d" % ntype
        return NodeType.symbol[ntype]

class Node:
    ntype = None
    id = None
    children = []
    litSet = set([])
    varSet = set([])
    # Corresponding schema node
    snode = None

    def __init__(self, ntype, id, children):
        self.ntype = ntype
        self.id = id
        self.children = children
        self.litSet = set([])
        self.varSet = set([])
        self.snode = None
        
    def getVars(self):
        if len(self.children) == 0:
            return
        self.litSet = set([])
        self.varSet = set([])
        for c in self.children:
            self.litSet |= c.litSet
            self.varSet |= c.varSet

    def clone(self, nid):
        return self

    def cstring(self):
        slist = ["N%d" % c.id for c in self.children]
        return '(' + ", ".join(slist) + ')'

    def __str__(self):
        return "N%d:%s%s" % (self.id, NodeType.name(self.ntype), self.cstring())

    def show(self):
        print("%s  Lits = %s, Vars = %s" % (str(self), str(self.litSet), str(self.varSet)))

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
        self.getVars()
        
    def clone(self, nid):
        nchildren = list(self.children)
        nnode = AndNode(nid, nchildren)
        return nnode


# Attempt optimizations
def optAndNode(id, children):
    # Look for simplifications
    if len(children) == 0:
        return ConstantNode(id, 1)
    if len(children) == 1:
        return children[0]
    return AndNode(id, children)


class OrNode(Node):

    splitVar = None

    def __init__(self, id, children, splitVar):
        # Put tchild first:
        if -splitVar in children[0].litSet:
            children.reverse()
        Node.__init__(self, NodeType.disjunction, id, children)
        self.splitVar = splitVar
        self.getVars()

    def clone(self, nid):
        nchildren = list(self.children)
        nnode = OrNode(nid, nchildren, self.splitVar)
        return nnode


def optOrNode(id, children, splitVar):
    if len(children) == 0:
        return ConstantNode(id, 0)
    if len(children) == 1:
        return children[0]
    return OrNode(id, children, splitVar)

class LeafNode(Node):
    
    lit = None
    def __init__(self, id, lit):
        Node.__init__(self, NodeType.leaf, id, [])
        self.lit = lit
        self.litSet = set([lit])
        self.varSet = set([abs(lit)])
        
    def clone(self, nid):
        return LeafNode(self, nid, self.lit)

    def cstring(self):
        return '(' + str(self.lit) + ')'

class ConstantNode(Node):

    val = None
    def __init__(self, id, val):
        Node.__init__(self, NodeType.constant, id, [])
        self.val = val

    def clone(self, nid):
        return ConstantNode(self, nid, self.val)

    def cstring(self):
        return str(self.val)

class IteNode(Node):

    splitVar = None
    
    def __init__(self, id, children, splitVar):
        Node.__init__(self, NodeType.ite, id, children)
        self.splitVar = splitVar
        self.getVars()
        self.litSet |= set([splitVar, -splitVar])
        self.varSet |= set([splitVar])

    def cstring(self):
        s = Node.cstring(self)
        return '(V' + str(self.splitVar) + ', ' + s[1:]

class Nnf:
    verbose = False
    inputCount = 0
    # Nodes are topologically ordered but their ids don't necessarily
    # match position in the array, nor are they necessarily in
    # ascending order
    nodes = []

    def __init__(self, verbose = False):
        self.inputCount = 0
        self.nodes = []

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
            line = trim(line)
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
                    print("Line #%d (%s).  Invalid header" % (lineNumber, line))
                    return False
            elif not gotHeader:
                print("Line #%d.  No header found" % (lineNumber))
            elif fields[0] == 'L':
                lit = 0
                if len(fields) != 2:
                    print("Line #%d (%s).  Literal declaration should contain one argument" % (lineNumber, line))
                    return False
                try:
                    lit = int(fields[1])
                except:
                    print("Line #%d (%s).  Invalid literal" % (lineNumber, line))
                    return False
                var = abs(lit)
                if var < 1 or var > self.inputCount:
                    print("Line #%d (%s).  Out of range literal" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = LeafNode(id, lit)
                nodeDict[id] = nnode
            elif fields[0] == 'A':
                try:
                    vals = [int(f) for f in fields[1:]]
                except:
                    print("Line #%d (%s).  Nonnumeric argument" % (lineNumber, line))
                    return False
                if len(vals) == 0 or vals[0] != len(vals)-1:
                    print("Line #%d (%s).  Incorrect number of arguments" % (lineNumber, line))
                    return False
                try:
                    children = [nodeDict[i] for i in vals[1:]]
                except:
                    print("Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = optAndNode(id, children)
                nodeDict[id] = nnode
            elif fields[0] == 'O':
                try:
                    vals = [int(f) for f in fields[1:]]
                except:
                    print("Line #%d (%s).  Nonnumeric argument" % (lineNumber, line))
                    return False
                if len(vals) < 2 or vals[1] != len(vals)-2:
                    print("Line #%d (%s).  Incorrect number of arguments (%d)" % (lineNumber, line, len(vals)))
                    return False
                nnode = None
                splitVar = vals[0]
                try:
                    children = [nodeDict[i] for i in vals[2:]]
                except:
                    print("Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = optOrNode(id, children, splitVar)
                nodeDict[id] = nnode
        if not gotHeader:
            print("No header found")
            return False
        # Compress into list
        self.nodes = []
        for id in sorted(nodeDict.keys()):
            node = nodeDict[id]
            if id == node.id:
                self.nodes.append(node)
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
        if self.verbose:
            print("Topological sort:")
            self.nodes.show()
        
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

    def findIte(self):
        idList = [node.id for node in self.nodes]
        nodeDict = { node.id  : node for node in self.nodes }
        # Mapping from old Id to new one for nodes that are replaced
        remap = {}
        for id in idList:
            node = nodeDict[id]
            node.children = [nodeDict[remap[child.id]] for child in node.children]
            if node.ntype != NodeType.disjunction:
                id = node.id
                remap[id] = id
                continue
            splitVar = node.splitVar
            tchild, fchild = nodeDict[node.children[0].id], nodeDict[node.children[1].id]
            tnode = None
            fnode = None
            if tchild.ntype == NodeType.leaf:
                if tchild.lit != splitVar:
                    print("WARNING: Expected literal %d in ITE argument %s" % (splitVar, str(tchild)))
                else:
                    nid = len(nodeDict)
                    tnode = ConstantNode(nid, 1)
                    nodeDict[nid] = tnode
                    remap[nid] = nid
            elif tchild.ntype == NodeType.conjunction:
                nchildren = []
                for c in tchild.children:
                    if c.ntype != NodeType.leaf or abs(c.lit) != splitVar:
                        nchildren.append(c)
                if len(nchildren) == 1:
                    tnode = nchildren[0]
                elif len(nchildren) != len(tchild.children)-1:
                    print("WARNING: Didn't find literal %d in ITE argument %s" % (splitVar, str(tchild)))
                else:
                    nid = len(nodeDict)
                    tnode = AndNode(nid, nchildren)
                    nodeDict[nid] = tnode
                    remap[nid] = nid
            if fchild.ntype == NodeType.leaf:
                if fchild.lit != -splitVar:
                    print("WARNING: Expected literal %d in ITE argument %s" % (-splitVar, str(fchild)))
                else:
                    nid = len(nodeDict)
                    fnode = ConstantNode(nid, 1)
                    nodeDict[nid] = fnode
                    remap[nid] = nid
            elif fchild.ntype == NodeType.conjunction:
                nchildren = []
                for c in fchild.children:
                    if c.ntype != NodeType.leaf or abs(c.lit) != splitVar:
                        nchildren.append(c)
                if len(nchildren) == 1:
                    fnode = nchildren[0]
                elif len(nchildren) != len(fchild.children)-1:
                    print("WARNING: Didn't find literal %d in ITE argument %s" % (-splitVar, str(fchild)))
                else:
                    nid = len(nodeDict)
                    fnode = AndNode(nid, nchildren)
                    nodeDict[nid] = fnode
                    remap[nid] = nid
            if tnode is not None and fnode is not None:
                nid = len(nodeDict)
                nnode = IteNode(nid, [tnode, fnode], splitVar)
                remap[nid] = nid
                remap[node.id] = nid
                nodeDict[nid] = nnode
        # Compress into list
        root = nodeDict[remap[self.nodes[-1].id]]
        self.nodes = []
        for id in sorted(nodeDict.keys()):
            node = nodeDict[id]
            if id == node.id:
                self.nodes.append(node)
        self.topoSort(root)

    def schematize(self, clauseList, fname):
        sch = schema.Schema(self.inputCount, clauseList, fname, verbLevel == 3 if self.verbose else 1)
        for node in self.nodes:
            if node is None:
                continue
            schildren = [child.snode for child in node.children]
            if node.ntype == NodeType.constant:
                node.snode = sch.leaf1 if node.val == 1 else sch.leaf0
            elif node.ntype == NodeType.leaf:
                var = abs(node.lit)
                svar = sch.getVariable(var)
                node.snode = svar if var > 0 else sch.addNegation(svar)
            elif node.ntype == NodeType.conjunction:
                # Build linear chain.   Keep literals at top
                schildren.reverse()
                nroot = schildren[0]
                for c in schildren[1:]:
                    nroot = sch.addConjunction(c, nroot)
                node.snode = nroot
            elif node.ntype == NodeType.disjunction:
                node.snode = sch.addDisjunction(schildren[0], schildren[1])
            elif node.ntype == NodeType.ite:
                svar = sch.getVariable(node.splitVar)
                node.snode = sch.addIte(svar, schildren[0], schildren[1])
                # Label for proof generation
                node.snode.iteVar = node.splitVar
#            print("NNF node %s --> schema node %s" % (str(node), str(node.snode)))
        return sch
                
def run(name, args):
    verbose = False
    cnfName = None
    nnfName = None
    cratName = None
    optlist, args = getopt.getopt(args, 'hvi:n:p:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-i':
            cnfName = val
        elif opt == '-n':
            nnfName = val
        elif opt == '-p':
            cratName = val
        else:
            print("Invalid option '%s'" % (opt))
            return
    if cnfName is None:
        print("Must give name of CNF file")
        return
    try:
        cnffile = open(cnfName, 'r')
    except:
        print("Couldn't open CNF file %s" % cnfName)
    creader = readwrite.CnfReader(cnfName, verbLevel = 3 if verbose else 1)
    if nnfName is None:
        print("Must give name of NNF file")
        return
    try:
        nfile = open(nnfName, 'r')
    except:
        print("Couldn't open NNF file %s" % nnfName)
    
    dag = Nnf(verbose)
    if not dag.read(nfile):
        print("Read failed")
    else:
        print("DAG has %d inputs, %d nodes" % (dag.inputCount, dag.nodeCount()))
    if verbose:
        dag.show()
        print("")
        print("ITE extraction:")
    dag.findIte()
    print("Resulting DAG has %d nodes" % (dag.nodeCount()))
    if verbose:
        dag.show()
    if cratName is not None:
        sch = dag.schematize(creader.clauses, cratName)
        if verbose:
            sch.show()
        sch.doValidate()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
