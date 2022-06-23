#!/usr/bin/python3

# Convert DNNF representation of Boolean formula into a counting schema

import sys
import getopt
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
    print("Usage: %s [-h] [-v] [-p] -n N [-i FILE.cnf] [-p FILE.nnf] [-o FILE.crat]")
    print(" -h           Print this message")
    print(" -v           Add comments to files")
    print(" -i FILE.cnf  Input CNF")
    print(" -p FILE.nnf  Input NNF")
    print(" -o FILE.crat Output CRAT")

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

    def __init__(self, ntype, id, children):
        self.ntype = ntype
        self.id = id
        self.children = children
        self.litSet = set([])
        self.varSet = set([])
        
    def getVars(self):
        if len(self.children) == 0:
            return
        self.litSet = set([])
        self.varSet = set([])
        for c in self.children:
            c.getVars()
            self.litSet |= c.litSet
            self.varSet |= c.varSet

    def cstring(self):
        slist = ["N%d" % c.id for c in self.children]
        return '(' + ", ".join(slist) + ')'

    def __str__(self):
        return "N%d:%s%s" % (self.id, NodeType.name(self.ntype), self.cstring())

    def show(self):
        print("%s  Lits = %s, Vars = %s" % (str(self), str(self.litSet), str(self.varSet)))

class AndNode(Node):
    
    def __init__(self, id, children):
        Node.__init__(self, NodeType.conjunction, id, children)
        self.getVars()

class OrNode(Node):

    splitVar = None

    def __init__(self, id, children, splitVar):
        Node.__init__(self, NodeType.disjunction, id, children)
        self.splitVar = splitVar
        self.getVars()

class LeafNode(Node):
    
    lit = None
    def __init__(self, id, lit):
        Node.__init__(self, NodeType.leaf, id, [])
        self.lit = lit
        self.litSet = set([lit])
        self.varSet = set([abs(lit)])
        
    def cstring(self):
        return '(' + str(self.lit) + ')'

class ConstantNode(Node):

    val = None
    def __init__(self, id, val):
        Node.__init__(self, NodeType.constant, id, [])
        self.val = val

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
    nodes = []

    def __init__(self, verbose = False):
        self.inputCount = 0
        self.nodes = []
    
    def nodeCount(self):
        count = 0
        for node in self.nodes:
            if node is not None:
                count += 1
        return count

    def read(self, infile):
        lineNumber = 0
        gotHeader = False
        ncount = 0
        ecount = 0
        self.nodes = []
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
                self.nodes.append(LeafNode(len(self.nodes), lit))
                
            elif fields[0] == 'A':
                try:
                    vals = [int(f) for f in fields[1:]]
                except:
                    print("Line #%d (%s).  Nonnumeric argument" % (lineNumber, line))
                    return False
                if len(vals) == 0 or vals[0] != len(vals)-1:
                    print("Line #%d (%s).  Incorrect number of arguments" % (lineNumber, line))
                    return False
                if vals[0] == 0:
                    self.nodes.append(ConstantNode(len(self.nodes), 1))
                else:
                    try:
                        children = [self.nodes[i] for i in vals[1:]]
                    except:
                        print("Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                        return False
                    self.nodes.append(AndNode(len(self.nodes), children))
            elif fields[0] == 'O':
                try:
                    vals = [int(f) for f in fields[1:]]
                except:
                    print("Line #%d (%s).  Nonnumeric argument" % (lineNumber, line))
                    return False
                if len(vals) != 2 and not (len(vals) == 4  and vals[2] != 2):
                    print("Line #%d (%s).  Incorrect number of arguments" % (lineNumber, line))
                    return False
                nnode = None
                splitVar = vals[0]
                if vals[1] == 0:
                    nnode = ConstantNode(len(self.nodes), 0)
                else:
                    try:
                        children = [self.nodes[i] for i in vals[2:]]
                    except:
                        print("Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                        return False
                    nnode = OrNode(len(self.nodes), children, splitVar)
                self.nodes.append(nnode)
        if not gotHeader:
            print("No header found")
            return True
        return True

    def show(self):
        for n in self.nodes:
            if n is not None:
                n.show()

    def findIte(self):
        newNodes = []
        for id in range(len(self.nodes)):
            node = self.nodes[id]
            if node is None or node.ntype != NodeType.disjunction:
                newNodes.append(node)
                continue
            splitVar = node.splitVar
            if splitVar in node.children[0].litSet:
                tchild, fchild = newNodes[node.children[0].id], newNodes[node.children[1].id] 
            else:
                tchild, fchild = newNodes[node.children[1].id], newNodes[node.children[0].id] 
            tnode = None
            fnode = None
            if tchild.ntype == NodeType.leaf:
                tnode = ConstantNode(tchild.id, 1)
            elif tchild.ntype == NodeType.conjunction:
                newArgs = []
                for c in tchild.children:
                    if c.ntype == NodeType.leaf or abs(c.lit) != splitVar:
                        newArgs.append(c)
                tnode = AndNode(tchild.id, newArgs)
            if fchild.ntype == NodeType.leaf:
                fnode = ConstantNode(fchild.id, 0)
            elif fchild.ntype == NodeType.conjunction:
                newArgs = []
                for c in fchild.children:
                    if c.ntype == NodeType.leaf or abs(c.lit) != splitVar:
                        newArgs.append(c)
                fnode = AndNode(fchild.id, newArgs)
            if tnode is not None and fnode is not None:
                node = IteNode(node.id, [tnode, fnode], splitVar)
            newNodes.append(node)
        return self.streamline(newNodes)

    def streamline(self, nodes):
        # Step 1: Remove single-argument Ands
        remap = {}
        for node in nodes:
            if node is None:
                continue
            elif node.ntype == NodeType.conjunction and len(node.children) == 1:
                remap[node.id] = node.children.id
            else:
                remap[node.id] = node.id
            newChildren = []
            for c in node.children:
                newChildren.append(nodes[remap[c.id]])
            node.children = newChildren

        # Step 2: Remove unreachable nodes
        marked = set([])
        check = set([len(nodes)-1])
        while len(check) > 0:
            id = check.pop()
            marked.add(id)
            node = nodes[id]
            for c in node.children:
                cid = c.id
                if cid not in marked and cid not in check:
                    check.add(cid)

        # Step 3: Create new version of nodes
        ndag = Nnf(self.verbose)
        ndag.inputCount = self.inputCount
        for node in nodes:
            if node is None or len(ndag.nodes) not in marked:
                ndag.nodes.append(None)
            else:
                ndag.nodes.append(node)
        return ndag
                
def run(name, args):
    verbose = False
    cnfName = None
    nnfName = None
    cratName = None
    optlist, args = getopt.getopt(args, 'hvi:p:o:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            nnfName = val
        elif opt == '-o':
            cratName = val
        else:
            print("Invalid option '%s'" % (opt))
            return
#    if cnfName is None:
#        print("Must give name of CNF file")
#        return
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
    dag = dag.findIte()
    print("Streamlined DAG has %d nodes" % (dag.nodeCount()))
    if verbose:
        dag.show()
    


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
