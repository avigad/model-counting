#!/usr/bin/python

# Representation of logic circuit as AIG

import sys

class AigRef:
    node = None
    negate = False

    def __init__(self, node, negate):
        self.node = node
        self.negate = negate

    def encode(self):
        return 2 * self.node.id + (1 if self.negate else 0)

    def isZero(self):
        return self.node.id == 0 and not self.negate

    def isOne(self):
        return self.node.id == 0 and self.negate

    def __str__(self):
        if self.isZero():
            return "0"
        elif self.isOne():
            return "1"
        else:
            return ("!" if self.negate else "") + str(self.node.id)

    def __eq__(self, other):
        return self.node == other.node and self.negate == other.negate

    def __hash__(self):
        return self.encode()

# Represent either AND node or input node
class AigNode:

    id = 0
    children = []           # AigRefs of children.  Empty if input node
    isInput = False

    def __init__(self, id, children):
        self.id = id
        self.children = children
        self.isInput = len(children) == 0

    # Generate string representing declaration line
    def declare(self):
        ilist = [2*self.id] + [c.encode() for c in self.children]
        slist = [str(i) for i in ilist]
        return " ".join(slist)

    def __str__(self):
        if len(self.children) > 1:
            return "%d = %s & %s" % (self.id, str(self.children[0]), str(self.children[1]))
        else:
            return "%d = input" % (self.id)

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

# Restricted form of AIG, only having combinational circuit
class AiGraph:
    
    inputs = []
    outputs = []
    gates = []  # Set of all gates, including constant zero
    gateMap = {} # Mapping from ref X ref --> gate
    nextId = 1
    comments = [] # Lines of comment text
    zeroRef = None # Ref representing constant zero
    oneRef = None # Ref representing constant one
    
    def __init__(self, inputCount):
        self.outputs = []
        cnode = AigNode(0, [])
        self.gates = [cnode]
        self.refMap = {}
        self.comments = []
        self.nextId = 1
        self.zeroRef = self.makeRef(cnode, False)
        self.oneRef = self.makeRef(cnode, True)
        self.inputs = [self.makeRef(self.newNode([]), False) for id in range(inputCount)]
        
    def newNode(self, children):
        node = AigNode(self.nextId, children)
        self.nextId += 1
        self.gates.append(node)
        return node

    def makeRef(self, node, negate):
        return AigRef(node, negate)

    def makeOutput(self, ref):
        self.outputs.append(ref)

    # Generate and of two refs.
    # Handle degenerate cases
    # Reuse existing gate if available
    def findOrMake(self, ref1, ref2):
        # Constant cases
        if ref1.isZero() or ref2.isZero():
            return self.zeroRef
        elif ref1.isOne():
            return ref2
        elif ref2.isOne():
            return ref1
        key = (ref1, ref2)
        if (ref1, ref2) not in self.gateMap:
            gate = self.newNode([ref1, ref2])
            self.gateMap[key] = gate
        return self.makeRef(self.gateMap[key], False)

    def negOp(self, ref):
        return AigRef(ref.node, not ref.negate)
        
    def andOp(self, ref1, ref2):
        ref = self.findOrMake(ref1, ref2)
        print("And(%s,%s)-->%s" % (str(ref1), str(ref2), str(ref)))
        return ref

    def orOp(self, ref1, ref2):
        nref1 = self.negOp(ref1)
        nref2 = self.negOp(ref2)
        return self.negOp(self.andOp(nref1, nref2))

    def iteOp(self, iref, tref, fref):
        if tref == fref:
            return tref
        hi = self.andOp(iref, tref)
        lo = self.andOp(self.negOp(iref), fref)
        return self.orOp(hi, lo)

    def comment(self, line):
        self.comments.append(line)
        
    def header(self, I):
        M = len(self.inputs)
        L = 0
        O = len(self.outputs)
        A = len(self.gates)-1
        ilist = [M, I, L, O, A]
        slist = ["aag"] + [str(i) for i in ilist]
        return " ".join(slist)

    def generate(self, outfile = sys.stdout):
        realInputs = set([])
        for oref in self.outputs:
            onode = oref.node
            if onode != self.gates[0] and onode.isInput and onode not in realInputs:
                realInputs |= { onode }
        for g in self.gates:
            for cref in g.children:
                c = cref.node
                if c != self.gates[0] and c.isInput and c not in realInputs:
                    realInputs |= { c }

        rlist = sorted([i for i in realInputs], key=lambda g: g.id)
                
        h = self.header(len(rlist))
        outfile.write(h + '\n')
        for inode in rlist:
            outfile.write(inode.declare() + '\n')
        for oref in self.outputs:
            outfile.write(str(oref.encode()) + '\n')
        for gnode in self.gates[1:]:
            if not gnode.isInput:
                outfile.write(gnode.declare() + '\n')
        if len(self.comments) > 1:
            outfile.write("c\n")
            for line in self.comments:
                outfile.write(line + '\n')
