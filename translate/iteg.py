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
        if tnode == enode:
            return tnode
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
        N = len(self.gates)
        ilist = [M, I, O, N]
        slist = ["iteg"] + [str(i) for i in ilist]
        return " ".join(slist)

    def generate(self, outfile = sys.stdout):
        if self.comments:
            for line in self.comments:
                outfile.write("c " + line + '\n')
        realInputs = set([])
        for onode in self.outputs:
            if onode.isInput and onode not in realInputs:
                realInputs |= { onode}
        for gnode in self.gates:
            for cnode in gnode.children:
                if cnode.isInput and cnode not in realInputs:
                    realInputs |= { cnode }
        rlist = sorted([i for i in realInputs], key=lambda g: g.id)
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
