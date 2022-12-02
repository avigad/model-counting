#!/usr/bin/python3


# Generate POG representation of formula based on trace of BDD evaluation
# btrace format contains following lines.  The only predefined nodes are leaves having Ids 1 and 0
#
# n  <Id> <Var> <Hi> <Lo>
# Node <Id> has variable <Var>, High child <Hi> and Low child <Lo>
#
# tc <Id> <Cid>
# Node <Id> is the BDD representation of input clause <Cid>
#
# a  <Rid> <Id1> <Id2>
# Node <Rid> represents the direct conjunction of nodes <Id1> and <Id2>
#
# ta <Rid> <Id1> <Id2>
# Node <Rid> is the BDD representation of the conjunction of BDDs <Id1> and <Id2>
#
# d  <Id>
# Node <Id> was deleted

import sys
import getopt

import readwrite
import bupog

def usage(name):
    print("Usage %s [-h] [-v VLEVEL] -i FILE.cnf -b FILE.btrace -p FILE.crat")
    print("  -h             Print this message")
    print("  -v VLEVEL      Set verbosity level")
    print("  -i FILE.cnf    Input formula")
    print("  -b FILE.btrace Trace of BDD execution")
    print("  -c FILE.crat   Output CRAT file")

class BtraceException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Btrace Exception: " + str(self.value)
    
          
class BddNode:

    id = None
    level = None
    high = None
    low = None
    pnode = None # Pog Node

    def __init__(self, id, level, high, low, pnode):
        self.id = id
        self.level = level
        self.high = high
        self.low = low
        self.pnode = pnode
        
# Simple manager for BDDs
class BddManager:
    pog = None
    # Mapping from BDD Ids to BDD nodes
    nodeMap = {}
    # Stack of commands to delete clauses and operations
    deletionStack = []
    
    def __init__(self, pog):
        self.pog = pog
        self.nodeMap = { }
        self.deletionStack = []
        self.leaf1 = BddNode(0, readwrite.tautologyId, 0, 0, pog.leaf0)
        self.leaf0 = BddNode(1, readwrite.tautologyId, 1, 1, pog.leaf1)
        self.store(self.leaf1)
        self.store(self.leaf0)

    def store(self, node):
        self.nodeMap[node.id] = node

    def getNode(self, id):
        if id not in self.nodeMap:
            raise BtraceException("Node with Id %d either never defined or deleted" % id)
        return self.nodeMap[id]

    def addNode(self, id, level, highId, lowId):
        hnode = self.getNode(highId)
        lnode = self.getNode(lowId)
        vpog = self.pog.findNode(level)
        hpog = hnode.pnode
        lpog = lnode.pnode
        pnode = self.pog.addIte(vpog, hpog, lpog)
        bnode = BddNode(id, level, hnode, lnode, pnode)
        if self.pog.verbLevel >= 2:
            self.pog.cwriter.doComment("BDD Node #%d represented by POG node %s" % (id, pnode.name()))
        self.store(bnode)

    def makeClause(self, lits, hints = None):
        cid = self.pog.cwriter.doClause(lits, hints)
        self.deletionStack.append((cid, hints))

    def justifyInput(self, rid, cid):
        # Will generate hints in future
        root = self.getNode(rid)
        lits = [root.pnode.xlit]
        if self.pog.verbLevel >= 2:
            self.pog.cwriter.doComment("Pog Node %s represents input clause #%d" % (root.pnode.name(), cid))
        self.makeClause(lits)
        self.pog.cwriter.doDeleteClause(cid, hints = None)

    def conjunctionResult(self, rid, id1, id2):
        root = self.getNode(rid)
        arg1 = self.getNode(id1)
        arg2 = self.getNode(id2)
        # Need to add hints
        lits = readwrite.cleanClause([-arg1.pnode.xlit, -arg2.pnode.xlit, root.pnode.xlit])
        if lits != readwrite.tautologyId:
            if self.pog.verbLevel >= 2:
                self.pog.cwriter.doComment("Justify %s & %s --> %s" % (arg1.pnode.name(), arg2.pnode.name(), root.pnode.name()))
            level = min(arg1.level, arg2.level)
            if level < readwrite.tautologyId:
                alits = readwrite.cleanClause([level, -arg1.pnode.xlit, -arg2.pnode.xlit, root.pnode.xlit])
                if alits != readwrite.tautologyId:
                    self.makeClause(alits, hints = None)
            self.makeClause(lits, hints = None)


    def justifyAnd(self, rid, id1, id2):
        root = self.getNode(rid)
        arg1 = self.getNode(id1)
        arg2 = self.getNode(id2)
        lits = [root.pnode.xlit]
        if self.pog.verbLevel >= 2:
            self.pog.cwriter.doComment("Justify %s = AND(%s, %s)" % (arg1.pnode.name(), arg2.pnode.name(), root.pnode.name()))
        self.makeClause(lits)
        
    def finish(self):
        self.deletionStack.reverse()
        if self.pog.verbLevel >= 2:
            self.pog.cwriter.doComment("Delete asserted clauses in reverse order")
        for cid, hints in self.deletionStack[1:]:
            self.pog.cwriter.doDeleteClause(cid, hints)
        self.pog.finish()

def processTrace(tfile, pog):
    mgr = BddManager(pog)
    lineCount = 0
    for line in tfile:
        line = readwrite.trim(line)
        lineCount += 1
        fields = line.split()
        if len(fields) == 0:
            continue
        cmd = fields[0]
        try:
            args = [int(field) for field in fields[1:]]
        except:
            print("Trace file line #%d.  Couldn't get integer arguments from line '%s'" % (lineCount, line))
            return False
        if cmd == 'n':
            if len(args) != 4:
                print("Trace file line #%d.  Invalid number of arguments in line '%s'" % (lineCount, line))
                return False
            try:
                mgr.addNode(args[0], args[1], args[2], args[3])
            except BtraceException as ex:
                print("Trace file line #%d.  Line = '%s'  Adding node failed: %s" % (lineCount, line, str(ex)))
                return False
        elif cmd == 'tc':
            if len(args) != 2:
                print("Trace file line #%d.  Invalid number of arguments in line '%s'" % (lineCount, line))
                return False
            try:
                mgr.justifyInput(args[0], args[1])
            except BtraceException as ex:
                print("Trace file line #%d.  Line = '%s'  Adding representation of input clause failed: %s" % (lineCount, line, str(ex)))
                return False
        elif cmd == 'a':
            if len(args) != 3:
                print("Trace file line #%d.  Invalid number of arguments in line '%s'" % (lineCount, line))
                return False
            try:
                mgr.conjunctionResult(args[0], args[1], args[2])
            except BtraceException as ex:
                print("Trace file line #%d.  Line = '%s'  Adding conjunction result failed: %s" % (lineCount, line, str(ex)))
                return False
        elif cmd == 'ta':
            if len(args) != 3:
                print("Trace file line #%d.  Invalid number of arguments in line '%s'" % (lineCount, line))
                return False
            try:
                mgr.justifyAnd(args[0], args[1], args[2])
            except BtraceException as ex:
                print("Trace file line #%d.  Line = '%s'  Adding conjunction result failed: %s" % (lineCount, line, str(ex)))
                return False
            
        else:
            print("Trace file line #%d.  Unknown command '%s'" % (lineCount, cmd))
    mgr.finish()
    return True

def run(name, args):
    verbLevel = 1
    cnfName = None
    btraceName = None
    cratName = None

    optlist, args = getopt.getopt(args, 'hv:i:b:c:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-b':
            btraceName = val
        elif opt == '-c':
            cratName = val

    if cnfName is None or btraceName is None or cratName is None:
        print("Require names for CNF file, btrace file, and CRAT file")
        usage(name)
        return

    creader = readwrite.CnfReader(cnfName, verbLevel)
    nvar = creader.nvar
    pog = bupog.Pog(nvar, creader.clauses, cratName, verbLevel)
    try:
        tfile = open(btraceName, 'r')
    except:
        print("Couldn't open trace file '%s'" % btraceName)
        return
    processTrace(tfile, pog)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
