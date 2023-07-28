# Perform projection operations

import os
import sys
import subprocess

import readwrite
import pog
import ddnnf
import cnf

class ProjectionException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Projection Exception: " + str(self.value)

# Create cache of previous solutions
# Indexed by both packed CNF representation and by previous POG

# CNF file stored in packed from
class PogCache:

    # Mapping from canonized CNF to POG
    clauseEntries = {}
    accessCount = 0
    missCount = 0

    def __init__(self):
        self.clauseEntries = {}
        self.accessCount = 0
        self.missCount = 0

    def insert(self, pcnf, pog):
        tup = pcnf.object()
        self.clauseEntries[tup] = pog

    def find(self, pcnf):
        self.accessCount += 1
        tup = pcnf.object()
        if tup  in self.clauseEntries:
            return self.clauseEntries[tup]
        else:
            self.missCount += 1
            return None

    def stats(self):
        return "POG Cache: %d entries.  %d accesses.  %d misses.  Miss rate = %.1f%%" % (
            len(self.clauseEntries), self.accessCount, self.missCount, 100.0 * self.missCount / self.accessCount)

pcache = PogCache()

class Projector:
    pog = None
    showVariables = None
    pcnf = None
    verbLevel = 1

    def __init__(self, pcnf, showVariables, verbLevel = 1):
        self.pcnf = pcnf
        self.showVariables = showVariables
        self.verbLevel = verbLevel
        self.pog = self.pcnf.makePog(self.verbLevel, trySimple = False)

    def traverseProduct(self, node, pcnf):
        if self.verbLevel >= 3:
            print("Product traversal of node %s" % node.string())
        contextLiterals = set([])
        nchildren = []
        nodeLits = []
        for child in node.children:
            if self.pog.isNode(child):
                nodeLits.append(child)
            else:
                contextLiterals.add(child)
                if abs(child) in self.showVariables:
                    nchildren.append(child)
        if len(nodeLits) == 1:
            cpcnf = pcnf.reduce(assignedLiterals = contextLiterals)
            nchild = self.traverse(nodeLits[0], cpcnf)
            nchildren.append(nchild)
        elif len(nodeLits) > 1:
            for nlit in nodeLits:
                cnode = self.pog.getNode(nlit)
                pvars = cnode.dependencySet(self.pog)
                cpcnf = pcnf.reduce(assignedLiterals = contextLiterals, partitionVariables = pvars)
                nclit = self.traverse(nlit, cpcnf)
                nchildren.append(nclit)
        nlit = self.pog.addProduct(nchildren)
        return nlit

    def traverseSum(self, node, pcnf):
        if self.verbLevel >= 3:
            print("Sum traversal of node %s" % node.string())
        nchildren = [self.traverse(child, pcnf) for child in node.children]
        dvar = node.findDecisionVariable(self.pog)
        if dvar is None:
            raise ProjectionException("Can't find decision variable for node %s" % node.string())
        nlit = None
        if dvar not in self.showVariables:
            if self.verbLevel >= 3:
                print("  Factoring decision variable %d" % dvar)
            mpcnf = pcnf.reduce(ignoredVariables = set([dvar]))
            if mpcnf.isSat():
                xpog = pcnf2ppog(mpcnf, self.showVariables, self.verbLevel)
                if (self.verbLevel >= 3):
                    print("  Exclusionary term")
                    xpog.show()
                xlit = self.pog.integrate(xpog)
                mlit = self.pog.addSum([-nchildren[0], xlit])
                nlit = self.pog.addSum([-mlit, nchildren[1]])
                if self.verbLevel >= 3:
                    print("   Traversing %s.  Integrated exclusionary term %d" % (node.string(), xlit))
            elif self.verbLevel >= 3:
                print("  Traversing %s.  Exclusionary term unsatisfiable" % (node.string()))
        if nlit is None:
            nlit = self.pog.addSum(nchildren)
        pcache.insert(pcnf, self.pog.extractSubgraph(nlit))
        return nlit


    # Given literal, replace by result of projection
    def traverse(self, lit, pcnf):
        if self.verbLevel >= 3:
            print("Traversing Pog literal %d" % lit)
        # Handle literals
        if not self.pog.isNode(lit):
            if abs(lit) in self.showVariables:
                if self.verbLevel >= 3:
                    print("  Literal %d preserved" % lit)
                return lit
            else:
                if self.verbLevel >= 3:
                    print("  Literal %d projected out" % lit)
                return self.pog.leaf1
        if self.verbLevel >= 3:
            print("CNF: %s" % str(pcnf.export()))
            self.pog.showSubgraph(lit)
        node = self.pog.getNode(lit)
        if lit < 0:
            raise ProjectionException("Can't handle negated node %s in traverse" % node.string())
        pcnf = purifyPcnf(pcnf, self.showVariables, self.verbLevel)
        pg = simplePog(pcnf, self.showVariables, self.verbLevel)
        if pg is not None:
            return self.pog.integrate(pg)
        if node.ntype == pog.NodeType.product:
            nlit = self.traverseProduct(node, pcnf)
        else:
            nlit = self.traverseSum(node, pcnf)
        if self.verbLevel >= 3:
            print("  Traversing Pog node %s yields literal %d" % (node.string(), nlit))
        if self.pog.isNode(nlit):
            npg = self.pog.extractSubgraph(nlit)
        return nlit
                
    def run(self):
        if self.verbLevel >= 2:
            sys.stdout.write("GEN: Initial POG: ")
            self.pog.summarize()
        if self.verbLevel >= 3:
            self.pog.show()
        nroot = self.traverse(self.pog.rootLiteral, self.pcnf)
        if self.verbLevel >= 3:
            print("GEN: Changed root literal from %d to %d" % (self.pog.rootLiteral, nroot))
        self.pog.setRoot(nroot)
        self.pog.compress()
        if self.verbLevel >= 2:
            sys.stdout.write("GEN: Projected POG: ") 
            self.pog.summarize()
        return self.pog
        
# Pure literal reduction
def purifyPcnf(pcnf, showVariables, verbLevel):
    plits = set([lit for lit in pcnf.pureLiterals() if abs(lit) not in showVariables])
    npcnf = pcnf
    if len(plits) > 0:
        if verbLevel >= 3:
            olits = sorted([lit for lit in plits], key = lambda lit : abs(lit))
            slist = [str(lit) for lit in olits]
            print("  Eliminate pure literals {%s}" % (", ".join(slist)))
        npcnf = pcnf.reduce(assignedLiterals = plits)
        if verbLevel >= 3:
            print("  Resulting CNF: %s" % str(pcnf.export()))
    return npcnf

# Simple POG generation cases
def simplePog(pcnf, showVariables, verbLevel):
    vars = pcnf.variables()
    if len(vars & showVariables) == 0:
        if verbLevel >= 3:
            print("  Simple POG: All variables projected.  Generating constant")
        root = readwrite.tautologyId if pcnf.isSat() else -readwrite.tautologyId
        return pog.leafPog(pcnf.nvar(), root)
    pg = pcache.find(pcnf)
    if pg is not None:
        if verbLevel >= 3:
            print("  Simple POG:  Found cached entry")
        return pg
    if vars <= showVariables:
        if verbLevel >= 3:
            print("  Simple Pog: All projection variables eliminated.  Generating POG representation")
            print("  CNF: %s" % str(pcnf.export()))
        # Already projected
        npg = pcnf.makePog(verbLevel, trySimple = True)
        if verbLevel >= 3:
            print("  Generated POG:")
            npg.show()
        pcache.insert(pcnf, npg)
        return npg
    return None


def pcnf2ppog(pcnf, showVariables, verbLevel):
    if verbLevel >= 3:
        vlist = sorted([v for v in showVariables])
        slist = [str(v) for v in vlist]
        print("Retaining variables {%s}" % ", ".join(slist))
    pcnf = purifyPcnf(pcnf, showVariables, verbLevel)
    pg = simplePog(pcnf, showVariables, verbLevel)
    if pg is not None:
        return pg
    pr = Projector(pcnf, showVariables, verbLevel)
    pg = pr.run()
    pcache.insert(pcnf, pg)
    return pg

