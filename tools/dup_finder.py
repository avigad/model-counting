#!/usr/bin/python3

# Given set of CNF files, print out equivalence classes of size > 1
# Does syntactic match of clauses

import sys
import readwrite

def usage(name):
    print("Usage: %s [-v] fname1 fname2 ..." % name)

def match(fname1, fname2):
    try:
        cnf1 = readwrite.CnfReader(fname1)
        cnf2 = readwrite.CnfReader(fname2)
    except Exception as ex:
        print("Oops.  Couldn't test match (%s).  Exiting" % str(ex))
        sys.exit(1)

    if cnf1.nvar != cnf2.nvar:
        return False
    if len(cnf1.clauses) != len(cnf2.clauses):
        return False
    for c1, c2 in zip(cnf1.clauses, cnf2.clauses):
        if len(c1) != len(c2):
            return False
        for lit1, lit2 in zip(c1, c2):
            if lit1 != lit2:
                return False
    return True

class Eclass:
    nvar = 0
    nclause = 0
    fnames = []

    def __init__(self, nvar = 0, nclause = 0):
        self.nvar = nvar
        self.nclause = nclause
        self.fnames = []
        
    def checkFile(self, fname, nvar, nclause):
        if self.nvar == 0:
            # First member of class
            self.nvar = nvar
            self.nclause = nclause
            self.fnames.append(fname)
            return True
        if nvar != self.nvar or nclause != self.nclause:
            return False
        if match(self.fnames[0], fname):
            self.fnames.append(fname)
            return True
        return False
        
    def show(self):
        return "{%s}" % ", ".join(self.fnames)

def build(fnames, verbose = False):
    classes = []
    for fname in fnames:
        found = False
        try:
            header = readwrite.CnfHeaderReader(fname)
        except Exception as ex:
            print("Oops.  Couldn't get header (%s).  Exiting" % str(ex))
            sys.exit(1)
        nvar = header.nvar
        nclause = header.nclause
        for eclass in classes:
            if eclass.checkFile(fname, nvar, nclause):
                found = True
                if verbose:
                    print("Found class %s" % eclass.show())
                break
        if not found:
            eclass = Eclass()
            eclass.checkFile(fname, nvar, nclause)
            classes.append(eclass)
            if verbose:
                print("Created class %s" % eclass.show())
    return classes

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        usage(name)
        return
    verbose = False
    if args[0] == '-v':
        verbose = True
        args = args[1:]
    classes = build(args, verbose)
    for eclass in classes:
        if len(eclass.fnames) > 1:
            print(" ".join(eclass.fnames))

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
            
    
