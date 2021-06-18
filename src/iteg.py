#!/usr/bin/python

# Representation of logic circuit as ITEG

import sys

def trim(s):
    while len(s) > 0 and s[-1] in '\n\r':
        s = s[:-1]
    return s

class IteException(Exception):

    msg = ""

    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "ITE Exception: " + self.msg

class ParseException(Exception):
    msg = ""
    line = 0

    def __init__(self, line, msg):
        self.msg = msg
        self.line = line
    
    def __str__(self):
        return "Parse ERROR.  Line %d.  %s" % (self.line, self.msg)

# Represent either ITE operation or input
class Node:

    id = 0
    children = []           # Children indices
    isZero = False
    isOne = False
    isInput = False
    isIte = False

    def __init__(self, id, children):
        if len(children) not in [0,3]:
            raise IteException("Cannot have %d children of a node" %len(children))
        if len(children) > 0 and max([c.id for c in children]) >= id:
            raise IteException("Children ID must be less than operator ID %d" % id)
        self.id = id
        self.children = children
        self.isZero = len(children) == 0 and id == 0
        self.isOne = len(children) == 0 and id == 1
        self.isInput = len(children) == 0 and id >= 2
        self.isIte = len(children) == 3

    def ilist(self):
        return  tuple([self.id] + [c.id for c in self.children])

    # Generate string representing declaration line
    def declare(self):
        slist = [str(i) for i in self.ilist()]
        return " ".join(slist)

    def __str__(self):
        if len(self.children) == 3:
            return "%d = ITE(%d, %d, %d)" % self.ilist()
        else:
            return "%d = Input" % (self.id)

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

# ITE Graph
class IteGraph:
    
    inputs = []
    outputs = []
    gates = []  # Set of all gates, including constants zero and one
    nextId = 2
    zeroNode = None # Representing constant zero
    oneNode = None  # Representing constant one
    nodeMap = {} # Mapping (i,t,e) --> ITE
    comments = []
    
    def __init__(self, inputCount):
        self.outputs = []
        self.gates = []
        self.nodeMap = {}
        self.outputs = []
        self.nextId = 2
        self.zeroNode = Node(0, [])
        self.oneNode = Node(1, [])
        self.comments = []
        self.inputs = [self.newNode([]) for idx in range(inputCount)]
        
    def newNode(self, children):
        node = Node(self.nextId, children)
        self.nextId += 1
        self.gates.append(node)
        return node

    def iteOp(self, inode, tnode, enode):
#        if tnode == enode:
#            return tnode
        key = (inode.id, tnode.id, enode.id)
        if key in self.nodeMap:
            return self.nodeMap[key]
        else:
            node = self.newNode([inode, tnode, enode])
            self.nodeMap[key] = node
            return node

    def makeOutput(self, node):
        self.outputs.append(node)

    def comment(self, line):
        self.comments.append(trim(line))
        
    def header(self, I):
        M = len(self.inputs)+1
        O = len(self.outputs)
        N = len(self.gates) - M + 1
        ilist = [M, I, O, N]
        slist = ["iteg"] + [str(i) for i in ilist]
        return " ".join(slist)

    def realInputs(self):
        rset = set([])
        for onode in self.outputs:
            if onode.isInput and onode not in rset:
                rset |= { onode}
        for gnode in self.gates:
            for cnode in gnode.children:
                if cnode.isInput and cnode not in rset:
                    rset |= { cnode }
        rlist = sorted([i for i in rset], key=lambda g: g.id)
        return rlist

    def generate(self, outfile = sys.stdout):
        if self.comments:
            for line in self.comments:
                outfile.write("c " + line + '\n')
        rlist = self.realInputs()
        h = self.header(len(rlist))
        outfile.write(h + '\n')
        outfile.write("c Input declarations\n")
        for inode in rlist:
            outfile.write(str(inode.id) + '\n')
        outfile.write("c Output declarations\n")
        for onode in self.outputs:
            outfile.write(str(onode.id) + '\n')
        outfile.write("c ITE operations\n")
        for gnode in self.gates:
            if gnode.isIte:
                outfile.write(gnode.declare() + '\n')

    def load(self, infile, prefix = None):
        maxIndex = None
        exInputCount = None
        exIteCount = None
        gotIteCount = 0
        exOutputCount = None
        inputIds = []
        outputIds = []
        lineNum = 0
        ngraph = None
        # Mapping for id to node
        idMap = {}
        for line in infile:
            lineNum += 1
            fields = line.split()
            if len(fields) == 0:
                continue
            if prefix is not None and fields[0] == prefix:
                fields = fields[1:]
            elif prefix is not None:
                # Not an ITEG line
                continue
            if fields[0][0] == 'c':
                continue
            elif maxIndex is None and fields[0] == 'iteg':
                try:
                    maxIndex, exInputCount, exOutputCount, exIteCount = [int(s) for s in fields[1:]]
                except:
                    raise ParseException(lineNum, "Couldn't parse iteg header")
                ngraph = IteGraph(maxIndex-1)
                idMap = { 0 : ngraph.zeroNode, 1: ngraph.oneNode }
                for node in ngraph.inputs:
                    idMap[node.id] = node
                continue
            if maxIndex is None:
                raise ParseException(lineNum, "No header detected")
            try:
                ilist = [int(s) for s in fields]
            except:
                raise ParseException(lineNum, "Non-numeric field")
            if len(inputIds) < exInputCount:
                if len(ilist) != 1:
                    raise ParseException(lineNum, "Expected input line with single integer")
                id = ilist[0]
                if id < 2 or id > maxIndex or id not in idMap:
                    raise ParseException(lineNum, "Invalid input id %d" % id)
                inputIds.append(id)
                continue
            if len(outputIds) < exOutputCount:
                if len(ilist) != 1:
                    raise ParseException(lineNum, "Expected output line with single integer")                    
                id = ilist[0]
                outputIds.append(id)
                continue
            if gotIteCount < exIteCount:
                if len(ilist) != 4:
                    raise ParseException(lineNum, "Expected 4 integers: o i t e")
                try:
                    i, t, e =  [idMap[v] for v in ilist[1:]]
                except:
                    raise ParseException(lineNum, "Invalid i, t, or e field")
                g = ngraph.iteOp(i, t, e)
                if g.id != ilist[0]:
                    raise ParseException(lineNum, "Wrong gate Id.  File id = %d.  Expected %d" % (ilist[0], g.id))
                idMap[g.id] = g
                gotIteCount += 1

        if exIteCount is None:
            raise ParseException(lineNum, "No ITEG declarations found")

        if gotIteCount != exIteCount:
            raise ParseException(lineNum, "Expected %d ITE gates.  Got %d" % (exIteCount, gotIteCount))
        for id in outputIds:
            try:
                node = idMap[id]
                ngraph.makeOutput(node)
            except:
                raise ParseException(lineNum, "Invalid output id %d" % id)

        return ngraph

    def genQbf(self, writer):
        inputIds = [n.id-1 for n in self.gates if n.isInput]
        writer.addVariables(0, inputIds, True)
        iteGates = [n for n in self.gates if n.isIte] 
        nodeIds = [n.id-1 for n in iteGates]
        writer.addVariables(1, nodeIds, True)
        # Generate clauses
        for n in iteGates:
            isRoot = n == iteGates[-1]
            inode, tnode, enode = n.children
            gid = n.id-1
            iid = inode.id-1
            tid = tnode.id-1
            eid = enode.id-1
            if tnode.isZero:
                writer.doClause([-iid, -gid])
            elif not tnode.isOne:
                writer.doClause([-iid, -gid, tid])
            if enode.isZero:
                writer.doClause([iid, -gid])
            elif not enode.isOne:
                writer.doClause([iid, -gid, eid])
            if isRoot:
                writer.doClause([gid])
        
    def genOrder(self, writer):
        iteGates = [n for n in self.gates if n.isIte] 
        nodeIds = [n.id-1 for n in iteGates]
        # Map from input Ids to all gate having this input
        levelMap = {}
        for n in iteGates:
            inode, tnode, enode = n.children
            gid = n.id-1
            iid = inode.id-1
            if iid in levelMap:
                levelMap[iid].append(gid)
            else:
                levelMap[iid] = [gid]
        iidList = sorted(levelMap.keys())
        for iid in iidList:
            writer.doOrder([iid] + levelMap[iid])

    # Compute number of models.  Must be Free ITEG (not checked)
    def countModels(self, node):
        if node == self.zeroNode:
            return 0
        if node == self.oneNode:
            return 2**len(self.inputs)
        ccounts = [self.countModels(child) for child in node.children[1:]]
        return sum(ccounts) // 2
        
