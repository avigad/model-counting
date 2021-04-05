# Representation of a Decision Diagram
# Can be ADD, BDD, ZDD
# ADD: Only consider ones with leaf values 0 and 1
# BDD: Can have negation pointers
# ZDD: Support zero-suppression rule

import aig
import iteg

def trim(s):
    while len(s) > 0 and s[-1] in '\n\r':
        s = s[:-1]
    return s

def getLine(infile, eofOK = False):
    while True:
        line = infile.readline()
        if len(line) == 0:
            if eofOK:
                return None
            else:
                raise Exception("Unexpected end of file")
        line = trim(line)
        if len(line) == 0:
            continue
        if line[0] == '#':
            continue
        return line


class DdException(Exception):

    msg = ""

    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "DD Exception: " + self.msg

class DdRef:
    node = None
    negate = False
    
    def __init__(self, node, negate=False):
        self.node = node
        self.negate = negate

    def encode(self):
        return 2 * self.node.id + (1 if self.negate else 0)

    def __str__(self):
        return ("!" if self.negate else "+") + str(self.node.id)

    def __eq__(self, other):
        return self.node == other.node and self.negate == other.negate

    def __hash__(self):
        return self.encode()


class DdNode:
    id = 0
    isLeaf = False

    def __init__(self, id, isLeaf):
        self.id = id
        self.isLeaf = isLeaf

    def __hash__(self):
        return self.id

    def __str__(self):
        return str(self.id)

class LeafNode(DdNode):
    value = 0

    def __init__(self, id, value):
        DdNode.__init__(self, id, True)
        self.value = value

class VarNode(DdNode):
    tvar = 0 # Integer top variable
    bvar = 0 # Integer bottome variable
    hi = None # References to children for BDD, otherwise children nodes
    lo = None # References to children for BDD, otherwise children nodes
    
    def __init__(self, id, var, hi, lo, bvar = None):
        DdNode.__init__(self, id, False)
        self.tvar = var
        self.hi = hi
        self.lo = lo
        self.bvar = var if bvar is None else bvar
    
class Dd:
    ddType = 'B' # Can be A or Z
    varList = []
    leafZero = None
    leafOne = None
    varNodes = []
    root = None
    nextId = 1
    isChained = False

    def __init__(self, ddType, varList = []):
        self.ddType = ddType
        self.varNodes = []
        self.varList = list(varList)
        self.root = None
        if self.ddType == 'B':
            cnode = LeafNode(0, 1)
            self.leafOne = DdRef(cnode, False)
            self.leafZero = DdRef(cnode, True)
            self.nextId = 2
        else:
            self.leafOne = LeafNode(0, 1)
            self.leafZero = LeafNode(1, 0)
            self.nextId = 3
        self.isChained = False

    def addVar(self, id):
        self.varList.append(id)

    def addNode(self, var, hi, lo, bvar = None, skipDC = False):
        if skipDC and hi == lo:
            return hi
        node = VarNode(self.nextId, var, hi, lo, bvar)
        self.nextId += 1

        self.varNodes.append(node)
        if node.tvar != node.bvar:
            self.isChained = True
        return node

    def makeRoot(self, node):
        self.root = node

    def readDd(self, infile):
        header = getLine(infile)
        fields = header.split()
        if len(fields) != 5:
            raise DdException("Invalid DD header line '%s'" % header)
        t = fields[0]
        if t not in "BZA":
            raise DdException("Invalid DD type '%s'" % t)        
        newDd = self if t == self.ddType else Dd(t)
        try:
            ilist = [int(s) for s in fields[1:]]
        except:
            raise DdException("Invalid DD header values '%s'" % header)
        vcount, lcount, ncount, rootId = ilist
        rootNegate = rootId < 0
        rootId = abs(rootId)
        minVar = None
        maxVar = None
        for idx in range(vcount):
            try:
                s = getLine(infile)
                v = int(s)
            except Exception as ex:
                raise DdException("Invalid variable #%d declaration (%s)" % (idx+lcount, str(ex)))
            minVar = v if minVar is None else min(minVar, v)
            maxVar = v if maxVar is None else max(maxVar, v)
        for v in range(minVar, maxVar+1):
            newDd.addVar(v)
        elcount = (1 if newDd.ddType == 'B' else 2)
        if lcount != elcount:
            raise DdException("Expected %d leaf values")
        nodeMap = {}
        for idx in range(lcount):
            line = getLine(infile)
            try:
                ifields = [int(s) for s in line.split()]
            except Exception as ex:
                raise DdException("Invalid leaf #%d declaration (%s)" % (idx+lcount, str(ex)))
            if len(ifields) != 2:
                raise DdException("Invalid leaf #%d line '%s'" % (idx+lcount, line))
            if newDd.ddType == 'B':
                nodeMap[ifields[0]] = newDd.leafOne.node
            else:
                if ifields[1] not in [0,1]:
                    raise DdException("Invalid leaf #%d value %d" % (idx+lcount, ifields[1]))
                nodeMap[ifields[0]] = newDd.leafZero if ifields[1] == 0 else newDd.leafOne
        for idx in range(ncount-lcount):
            line = getLine(infile)
            fields = line.split()
            if len(fields) != 4:
                raise DdException("Invalid node #%d line '%s'" % (idx+lcount, line))            
            try:
                index = int(fields[0])
                vfields = fields[1].split(":")
                if len(vfields) == 2:
                    tvar, bvar = [int(v) for v in vfields]
                else:
                    tvar = int(vfields[0])
                    bvar = tvar
                tchild = int(fields[2])
                tnegate = tchild < 0
                tchild = abs(tchild)
                echild = int(fields[3])
                enegate = echild < 0
                echild = abs(echild)
            except Exception as ex:
                raise DdException("Invalid node #%d declaration '%s' (%s)" % (idx+lcount, line, str(ex)))
            try:
                tnode = nodeMap[tchild]
            except:
                raise DdException("Invalid node #%d child %d" % (idx+lcount, tchild))
            try:
                enode = nodeMap[echild]
            except:
                raise DdException("Invalid node #%d child %d" % (idx+lcount, echild))
            if newDd.ddType == 'B':
                tref = DdRef(tnode, tnegate)
                eref = DdRef(enode, enegate)
            else:
                tref = tnode
                eref = enode
            nnode = newDd.addNode(tvar, tref, eref, bvar)
            nodeMap[index] = nnode
        rootNode = nodeMap[rootId]
        if newDd.ddType == 'B':
            root = DdRef(rootNode, rootNegate)
            newDd.makeRoot(root)
        else:
            newDd.makeRoot(rootNode)
        return newDd

    def writeDd(self, outfile):
        leafCount = 1 if self.ddType == 'B' else 2
        nodeCount = len(self.varNodes)+leafCount
        rootId = -nodeCount if self.ddType == 'B' and self.root.negate else nodeCount
        ifields = [len(self.varList), leafCount, nodeCount, rootId]
        if self.ddType == 'B':
            idDict = { self.leafOne.node : 1}
            leafLines = ["1 1"]
        else:
            idDict = { self.leafOne : 1, self.leafZero : 2}
            leafLines = ["1 1", "2 0"]
        hlist = [self.ddType] + [str(i) for i in ifields]
        outfile.write("# TYPE VARCOUNT LEAFCOUNT NODECOUNT ROOTID\n")
        outfile.write(" ".join(hlist) + '\n')
        outfile.write("# Variable list\n")
        for v in self.varList:
            outfile.write(str(v) + '\n')
        outfile.write("# Leaves: ID VALUE\n")
        for line in leafLines:
            outfile.write(line + '\n')
        outfile.write("# Nodes: ID INDICES TCHILD ECHILD\n")
        for idx in range(len(self.varNodes)):
            id = idx+leafCount+1
            n = self.varNodes[idx]
            idDict[n] = id
            if n.tvar == n.bvar:
                sindex = str(n.tvar)
            else:
                sindex = str(n.tvar) + ':' + str(n.bvar)
            if self.ddType == 'B':
                tchild = idDict[n.hi.node]
                if n.hi.negate:
                    tchild = -tchild
                echild = idDict[n.lo.node]
                if n.lo.negate:
                    echild = -echild
            else:
                tchild = idDict[n.hi]
                echild = idDict[n.lo]
            sfields = [str(id), sindex, str(tchild), str(echild)]
            outfile.write(" ".join(sfields) + '\n')

    # Delete anything not reachable from root
    def prune(self):
        if self.root is None:
            raise DdException("Cannot prune without root")
        if self.ddType not in ['A', 'Z']:
            raise DdException("Only support pruning of ADDs and ZDDs")
        if self.root.isLeaf:
            return self
        activeSet = { self.root }
        visitList = [self.root]
        doneList = []
        while len(visitList) > 0:
            n = visitList[0]
            visitList = visitList[1:]
            doneList.append(n)
            if n.isLeaf:
                continue
            if n.hi not in activeSet and not n.hi.isLeaf:
                activeSet |= { n.hi }
                visitList.append(n.hi)
            if n.lo not in activeSet and not n.lo.isLeaf:
                activeSet |= { n.lo }
                visitList.append(n.lo)
        if len(activeSet) == len(self.varNodes):
            # No pruning needed
            return self
        newDd = Dd(self.ddType, self.varList)
        remap = {self.leafZero:newDd.leafZero, self.leafOne:newDd.leafOne}
        doneList.reverse()
        for n in doneList:
            newhi = remap[n.hi]
            newlo = remap[n.lo]
            remap[n] = newDd.addNode(n.tvar, newhi, newlo, n.bvar)
        newDd.makeRoot(remap[self.root])
        return newDd

    # Generate a DD with chaining removed
    def dechain(self):
        if not self.isChained:
            # Nothing needed
            return self

        if not self.ddType == 'A':
            raise DdException("Only support dechaining of ADDs")

        newDd = Dd(self.ddType, self.varList)
        nodeDict = {} # Mapping (var, hi, lo) --> node for each node in new DD
        remap = { self.leafZero : newDd.leafZero, self.leafOne : newDd.leafOne }
        
        for n in self.varNodes:
            newhi = remap[n.hi]
            newlo = remap[n.lo]
            nnode = newlo
            for v in range(n.bvar, n.tvar-1, -1):
                key = (v, newhi, nnode)
                if key in nodeDict:
                    nnode = nodeDict[key]
                else:
                    nnode = newDd.addNode(v, newhi, nnode)
                    nodeDict[key] = nnode
            remap[n] = nnode
        if self.root is not None:
            newDd.makeRoot(remap[self.root])
        return newDd
    
    def bdd2add(self):
        newDd = Dd('A', self.varList)
        posMap = {self.leafOne.node:newDd.leafOne}
        negMap = {self.leafOne.node:newDd.leafZero}
        for n in self.varNodes:
            nphi = negMap[n.hi.node] if  n.hi.negate else posMap[n.hi.node]
            nplo = negMap[n.lo.node] if  n.lo.negate else posMap[n.lo.node]
            posMap[n] = newDd.addNode(n.tvar, nphi, nplo, n.bvar)
            nnhi = posMap[n.hi.node] if  n.hi.negate else negMap[n.hi.node]
            nnlo = posMap[n.lo.node] if  n.lo.negate else negMap[n.lo.node]
            negMap[n] = newDd.addNode(n.tvar, nnhi, nnlo, n.bvar)
        if self.root is not None:
            nroot = negMap[self.root.node] if self.root.negate else posMap[self.root.node]
            newDd.makeRoot(nroot)
        return newDd.prune()

    def zdd2add(self):
        newDd = Dd('A', self.varList)
        nodeDict = {} # Mapping (tvar, hi, lo, bvar) --> node for each node in new DD
        remap = { self.leafZero : newDd.leafZero, self.leafOne : newDd.leafOne }

        minVar = min(self.varList)
        maxVar = max(self.varList)

        for n in self.varNodes:
            nhi = remap[n.hi]
            nlo = remap[n.lo]
            # Insert zero chains to children
            ctvar = n.bvar+1
            cbvar = maxVar if n.hi.isLeaf else n.hi.tvar-1
            if nhi != newDd.leafZero and ctvar <= cbvar:
                key = (ctvar, newDd.leafZero, nhi, cbvar)
                if key in nodeDict:
                    nhi = nodeDict[key]
                else:
                    nhi = newDd.addNode(ctvar, newDd.leafZero, nhi, cbvar, skipDC = True)
                    nodeDict[key] = nhi
            cbvar = maxVar if n.lo.isLeaf else n.lo.tvar-1
            if nlo != newDd.leafZero and ctvar <= cbvar:
                key = (ctvar, newDd.leafZero, nlo, cbvar)
                if key in nodeDict:
                    nlo = nodeDict[key]
                else:
                    nlo = newDd.addNode(ctvar, newDd.leafZero, nlo, cbvar, skipDC = True)
                    nodeDict[key] = nlo
            # New node will come below any don't cares in ZDD
            key = (n.bvar, nhi, nlo, n.bvar)
            if key in nodeDict:
                remap[n] = nodeDict[key]
            else:
                remap[n] = newDd.addNode(n.bvar, nhi, nlo, n.bvar, skipDC = True)
        if self.root is not None:
            # Root should have zero chain in front
            nroot = remap[self.root]
            ctvar = minVar
            cbvar = maxVar if self.root.isLeaf else self.root.tvar-1
            if nroot != newDd.leafZero and ctvar <= cbvar:
                key = (ctvar, newDd.leafZero, nroot, cbvar)
                if key in nodeDict:
                    nroot = nodeDict[key]
                else:
                    nroot = newDd.addNode(ctvar, newDd.leafZero, nroot, cbvar, skipDC = True)
            newDd.makeRoot(nroot)
        return newDd
        
    def toAdd(self):
        if self.ddType == 'A':
            return self
        elif self.ddType == 'B':
            return self.bdd2add()
        elif self.ddType == 'Z':
            return self.zdd2add()

    def add2aig(self):
        if self.root is None:
            raise DdException("Need to have root declared")
        if self.ddType != 'A':
            raise DdException("Can only generated AIGs for ADDs")
        if self.isChained:
            raise DdException("Must remove chaining before convert to AIG")
        g = aig.AiGraph(len(self.varList))
        inputMap = { self.varList[idx] : g.inputs[idx] for idx in range(len(self.varList)) }
        nodeMap = { self.leafZero : g.zeroRef, self.leafOne : g.oneRef }
        for n in self.varNodes:
            iref = inputMap[n.tvar]
            tref = nodeMap[n.hi]
            eref = nodeMap[n.lo]
            nodeMap[n] = g.iteOp(iref, tref, eref)
        g.makeOutput(nodeMap[self.root])
        return g

    def add2iteg(self):
        if self.root is None:
            raise DdException("Need to have root declared")
        if self.ddType != 'A':
            raise DdException("Can only generated ITEGs for ADDs")
        if self.isChained:
            raise DdException("Must remove chaining before convert to ITEG")
        g = iteg.IteGraph(len(self.varList))
        inputMap = { self.varList[idx] : g.inputs[idx] for idx in range(len(self.varList)) }
        nodeMap = { self.leafZero : g.zeroNode, self.leafOne : g.oneNode }
        for n in self.varNodes:
            inode = inputMap[n.tvar]
            tnode = nodeMap[n.hi]
            enode = nodeMap[n.lo]
            nodeMap[n] = g.iteOp(inode, tnode, enode)
        g.makeOutput(nodeMap[self.root])
        return g
    
