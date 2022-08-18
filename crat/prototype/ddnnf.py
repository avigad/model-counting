#!/usr/bin/python3

# Convert DNNF representation of Boolean formula into a POG

import sys
import getopt
import datetime
import readwrite
import pog

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


def usage(name):
    print("Usage: %s [-h] [-d] [-v VLEVEL] [-i FILE.cnf] [-n FILE.nnf] [-c CFILE] [-p FILE.crat]")
    print(" -h           Print this message")
    print(" -d           Use NNF format defined for D4 model counter")
    print(" -v VLEVEL    Set verbosity level (0-3)")
    print(" -i FILE.cnf  Input CNF")
    print(" -n FILE.nnf  Input NNF")
    print(" -c CFILE     Read conflict clauses embedded in CFILE")
    print(" -p FILE.crat Output CRAT")

class NnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Nnf Exception: " + str(self.value)

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
    # Corresponding POG node
    snode = None

    def __init__(self, ntype, id, children):
        self.ntype = ntype
        self.id = id
        self.children = children
        self.snode = None
        
    def cstring(self):
        slist = ["N%d" % c.id for c in self.children]
        return '(' + ", ".join(slist) + ')'

    def __str__(self):
        return "N%d:%s%s" % (self.id, NodeType.name(self.ntype), self.cstring())

    def show(self):
        print(str(self))

    def findLit(self, var):
        return None

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
        
    def findLit(self, var):
        for c in self.children:
            lit = c.findLit(var)
            if lit is not None:
                return lit
        return None


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
    splitVar = None

    def __init__(self, id, children, splitVar):
        # Put tchild first:
        lit0 = children[0].findLit(splitVar)
        if lit0 is None:
            raise(NnfException("Couldn't find literal of variable %d in %s" % (splitVar, str(self))))
        if lit0 == -splitVar:
            children.reverse()
        Node.__init__(self, NodeType.disjunction, id, children)
        self.splitVar = splitVar

def optOrNode(id, children, splitVar):
    nchildren = []
    for child in children:
        if child.ntype == NodeType.constant:
            if child.val == 1:
                return child
        else:
            nchildren.append(child)
    if len(nchildren) == 0:
        return ConstantNode(id, 0)
    if len(nchildren) == 1:
        return nchildren[0]
    return OrNode(id, nchildren, splitVar)

class LeafNode(Node):
    
    lit = None
    def __init__(self, id, lit):
        Node.__init__(self, NodeType.leaf, id, [])
        self.lit = lit

    def cstring(self):
        return '(' + str(self.lit) + ')'

    def findLit(self, var):
        if abs(self.lit) == var:
            return self.lit
        return None

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

    def cstring(self):
        s = Node.cstring(self)
        return '(V' + str(self.splitVar) + ', ' + s[1:]

class Nnf:
    verbLevel = 1
    inputCount = 0
    # Nodes are topologically ordered but their ids don't necessarily
    # match position in the array, nor are they necessarily in
    # ascending order
    nodes = []

    def __init__(self, verbLevel = 1):
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
                splitVar = vals[0]
                try:
                    children = [nodeDict[i] for i in vals[2:]]
                except:
                    print("ERROR:Line #%d (%s) Invalid argument specifier" % (lineNumber, line))
                    return False
                id = len(nodeDict)
                nnode = optOrNode(id, children, splitVar)
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

    def findIte(self):
        # Look for constant 1 node
        k1 = None
        idList = [node.id for node in self.nodes]
        if len(idList) > 0:
            nextId = max(idList) + 1
        else:
            nextId = 1
        nodeDict = { node.id  : node for node in self.nodes }
        # Mapping from old Id to new one for nodes that are replaced
        remap = {}
        for id in idList:
            node = nodeDict[id]
            if node.ntype == NodeType.constant and node.val == 1:
                k1 = node
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
                    nid = nextId
                    nextId += 1
                    if k1 is None:
                        k1 = ConstantNode(nid, 1)
                    tnode = k1
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
                    nid = nextId
                    nextId += 1
                    tnode = AndNode(nid, nchildren)
                    nodeDict[nid] = tnode
                    remap[nid] = nid
            if fchild.ntype == NodeType.leaf:
                if fchild.lit != -splitVar:
                    print("WARNING: Expected literal %d in ITE argument %s" % (-splitVar, str(fchild)))
                else:
                    nid = nextId
                    nextId += 1
                    if k1 is None:
                        k1 = ConstantNode(nid, 1)
                    fnode = k1
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
                    nid = nextId
                    nextId += 1
                    fnode = AndNode(nid, nchildren)
                    nodeDict[nid] = fnode
                    remap[nid] = nid
            if tnode is not None and fnode is not None:
                nid = nextId
                nextId += 1
                nnode = IteNode(nid, [tnode, fnode], splitVar)
                remap[nid] = nid
                remap[node.id] = nid
                nodeDict[nid] = nnode
                if self.verbLevel >= 3:
                    print("Created Node #%d ITE(%d, %s, %s)" % (nid, splitVar, str(tnode), str(fnode)))
            else:
                raise NnfException("Couldn't convert node %s into ITE" % (node))
        # Compress into list
        root = nodeDict[remap[self.nodes[-1].id]]
        self.nodes = []
        for id in sorted(nodeDict.keys()):
            node = nodeDict[id]
            if id == node.id:
                self.nodes.append(node)
        self.topoSort(root)

    def makePog(self, clauseList, fname, conflictClauseList):
        pg = pog.Pog(self.inputCount, clauseList, fname, conflictClauseList, self.verbLevel)
        for node in self.nodes:
            schildren = [child.snode for child in node.children]
            if node.ntype == NodeType.constant:
                node.snode = pg.leaf1 if node.val == 1 else pg.leaf0
            elif node.ntype == NodeType.leaf:
                var = abs(node.lit)
                svar = pg.getVariable(var)
                node.snode = svar if node.lit > 0 else pg.addNegation(svar)
            elif node.ntype == NodeType.conjunction:
                # Build linear chain.   Keep literals at top
                nroot = pg.addConjunction(schildren)
                node.snode = nroot
            elif node.ntype == NodeType.disjunction:
                node.snode = pg.addDisjunction(schildren[0], schildren[1])
            elif node.ntype == NodeType.ite:
                svar = pg.getVariable(node.splitVar)
                node.snode = pg.addIte(svar, schildren[0], schildren[1])
                # Label for proof generation
                node.snode.iteVar = node.splitVar
            if self.verbLevel >= 3:
                print("NNF node %s --> POG node %s" % (str(node), str(node.snode)))
        pg.compress()
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
    def doDisjunction(self, args, splitVar):
        nextId = len(self.nnf.nodes)+1
        arg = optOrNode(nextId, args, splitVar)
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
            litsA = pchildren[0][1]
            litsB = pchildren[1][1]
            if len(litsA) > 0 and len(litsB) > 0 and litsA[0] == -litsB[0]:
                splitVar = abs(litsA[0])
            else:
                print("Or Operation #%d.  Couldn't find splitting variable" % pid)
                return False
            op = self.doDisjunction(achildren, splitVar)
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
        
        
def run(name, args):
    verbLevel = 1
    d4 = False
    cnfName = None
    nnfName = None
    cratName = None
    conflictName = None
    conflictClauses = []
    optlist, args = getopt.getopt(args, 'hdv:i:n:p:c:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-d':
            d4 = True
        elif opt == '-i':
            cnfName = val
        elif opt == '-n':
            nnfName = val
        elif opt == '-c':
            conflictName = val
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
    try:
        creader = readwrite.CnfReader(cnfName, verbLevel = verbLevel)
    except Exception as ex:
        print("ERROR in CNF File: %s" % str(ex))
        return
    if nnfName is None:
        print("Must give name of NNF file")
        return
    try:
        nfile = open(nnfName, 'r')
    except:
        print("Couldn't open NNF file %s" % nnfName)
        return
    
    if conflictName is not None:
        try:
            clauseReader = readwrite.ClauseReader(conflictName, "CRAT", verbLevel = verbLevel)
        except Exception as ex:
            print("ERROR in Conflict Clause File: %s" % str(ex))
            return
        conflictClauses = clauseReader.clauses

    start = datetime.datetime.now()
    dag = Nnf(verbLevel)
    if d4:
        d4reader = D4Reader(dag)
        if not d4reader.read(nfile):
            print("Read failed")
            return
        if not d4reader.build():
            print("Build failed")
            return
    elif not dag.read(nfile):
        print("Read failed")
        return
    elif verbLevel >= 1: 
       print("c Input NNF DAG has %d inputs, %d nodes" % (dag.inputCount, dag.nodeCount()))
    if verbLevel >= 3:
        dag.show()
    if verbLevel >= 2:
        print("")
        print("c ITE extraction:")
    dag.findIte()
    if verbLevel >= 1:
        print("c NNF DAG with ITEs has %d nodes" % (dag.nodeCount()))
    if verbLevel >= 2:
        dag.show()
    if cratName is not None:
        pg = dag.makePog(creader.clauses, cratName, conflictClauses)
        if verbLevel == 1:
            print("c Generated POG has %d nodes" % len(pg.nodes))
        if verbLevel >= 2:
            print("")
            print("c Generated POG has %d nodes:" % len(pg.nodes))
            pg.show()
        pg.doValidate()
        pg.finish()
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    print("Elapsed time for generation: %.2f seconds" % seconds)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
