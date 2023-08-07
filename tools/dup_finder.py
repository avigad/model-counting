#!/usr/bin/python3

# Given set of CNF files, print out equivalence classes of size > 1
# Does syntactic match of clauses

import sys
import shutil

import readwrite

def usage(name):
    print("Usage: %s [-h]  [-v] [-u PATH] fname1 fname2 ..." % name)
    print("  -h      Print this message")
    print("  -v      Verbose")
    print("  -u PATH  Make a copy of the first representative from each class in PATH")

# Global variables
verbose = False

# hash(clauses): hash each clause as a tuple, and hash clause hashes
def hashClauses(clauses):
    hlist = []
    for clause in clauses:
        hlist.append( hash(tuple(clause)))
    rval =  hash(tuple(hlist))
    return rval


def match(fname1, fname2):
    try:
        cnf1 = readwrite.CnfReader(fname1, check = False)
        cnf2 = readwrite.CnfReader(fname2, check = False)
    except Exception as ex:
        print("Oops.  Couldn't test match (%s).  Exiting" % str(ex))
        sys.exit(1)

    if cnf1.nvar != cnf2.nvar:
        return False
    if len(cnf1.clauses) != len(cnf2.clauses):
        return False
    sv1 = set([]) if cnf1.showVariables is None else cnf1.showVariables
    sv2 = set([]) if cnf2.showVariables is None else cnf2.showVariables
    if sv1 != sv2:
        return False
    for c1, c2 in zip(cnf1.clauses, cnf2.clauses):
        if len(c1) != len(c2):
            return False
        for lit1, lit2 in zip(c1, c2):
            if lit1 != lit2:
                return False
    return True

def stripPath(path):
    fields = path.split('/')
    return fields[-1]


class Eclass:
    nvar = 0
    nclause = 0
    chash = 0
    fnames = []

    def __init__(self, nvar = 0, nclause = 0, chash = 0):
        self.nvar = nvar
        self.nclause = nclause
        self.chash = chash
        self.fnames = []
        
    def checkFile(self, fname, nvar, nclause, chash):
        if self.nvar == 0:
            # First member of class
            self.nvar = nvar
            self.nclause = nclause
            self.chash = chash
            self.fnames.append(fname)
            return True
        if nvar != self.nvar or nclause != self.nclause or chash != self.chash:
            return False
        if match(self.fnames[0], fname):
            self.fnames.append(fname)
            return True
        return False
        
    def show(self):
#        return "%d variables, %d clauses, hash = %d,  {%s}" % (self.nvar, self.nclause, self.chash,  ", ".join(self.fnames))
        return "{%s}" % (", ".join(self.fnames))

    def uniqueCopy(self, path):
        src = self.fnames[0]
        dest = path + '/' + stripPath(src)
        if len(self.fnames) == 1:
                print("%s --> %s (Unique)" % (src, dest))
        else:
            print("%s --> %s (Duplicated by %s)" % (src, dest, ", ".join(self.fnames[1:])))
        shutil.copy(src, dest)




def build(fnames):
    # Mapping from hash of clauses to list of eclasses
    eclassDict = {}
    classes = []
    for fname in fnames:
        found = False
        try:
            cnf = readwrite.CnfReader(fname, check=False)
        except Exception as ex:
            print("Oops.  Couldn't get header (%s).  Exiting" % str(ex))
            sys.exit(1)
        nvar = cnf.nvar
        nclause = len(cnf.clauses)
        chash = hashClauses(cnf.clauses)
        if chash in eclassDict:
            for eclass in eclassDict[chash]:
                if eclass.checkFile(fname, nvar, nclause, chash):
                    found = True
                    if verbose:
                        print("Found class %s" % eclass.show())
                    break
        if not found:
            eclass = Eclass()
            classes.append(eclass)
            eclass.checkFile(fname, nvar, nclause, chash)
            if chash in eclassDict:
                eclassDict[chash].append(eclass)
            else:
                eclassDict[chash] = [eclass]
            if verbose:
                print("Created class %s" % eclass.show())
    return classes

def run(name, args):
    global verbose
    verbose = False
    path = None
    if len(args) == 0 or args[0] == '-h':
        usage(name)
        return
    verbose = False
    while args[0][0] == '-':
        if args[0] == '-v':
            verbose = True
            args = args[1:]
        elif args[0] == '-u':
            path = args[1]
            args = args[2:]
        else:
            print("Unknown flag '%s'" % args[0])
            return
    classes = build(args)
    for eclass in classes:
        if len(eclass.fnames) > 1:
            print("Class: " + " ".join(eclass.fnames))
        if path is not None:
            eclass.uniqueCopy(path)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)
    
