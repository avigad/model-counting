#!/usr/bin/python

# Translate different DD types into other DD types, as well as AIGs and ITEGs
# Possibilities:
# Chained BDD --> Chained ADD, Unchained ADD, AIG, ITEG
# Chained ZDD --> Chained ADD, Unchained ADD, AIG, ITEG
# Chained ADD --> Unchained ADD, AIG, ITEG

import getopt
import sys
import dd

def usage(name):
    print("Usage: %s [-h] [-c] [-a] [-i IFILE] ([-o OFILE]|[-A AFILE]|[-I ITEFILE])" % name)
    print(" -h         Print this message")
    print(" -c         Remove chaining")
    print(" -a         Convert to ADD")
    print(" -i IFILE   Input file")
    print(" -o OFILE   Output DD file")
    print(" -A AFILE   Output AIG file")
    print(" -I ITEFILE Output ITEG file")

def run(name, args):
    dechain = False
    makeAdd = False
    iname = "standard input"
    infile = sys.stdin
    outfile = sys.stdout
    aigfile = None
    itegfile = None

    optlist, args = getopt.getopt(args, "hcai:o:A:I:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-c':
            dechain = True
        elif opt == '-a':
            makeAdd = True
        elif opt == '-i':
            try:
                infile = open(val, 'r')
            except:
                print("Couldn't open input file '%s'" % val)
                return
            iname = val
        elif opt == '-o':
            try:
                outfile = open(val, 'w')
            except:
                print("Couldn't open output DD file '%s'" % val)
                return
        elif opt == '-A':
            try:
                makeAdd = True
                dechain = True
                aigfile = open(val, 'w')
                outfile = None
                itegfile = None
            except:
                print("Couldn't open output AIG file '%s'" % val)
                return
        elif opt == '-I':
            try:
                makeAdd = True
                dechain = True
                itegfile = open(val, 'w')
                outfile = None
                aigfile = None
            except:
                print("Couldn't open output ITEG file '%s'" % val)
                return
    newDd = dd.Dd('B')
    newDd = newDd.readDd(infile)
    if makeAdd:
        newDd = newDd.toAdd()
    if dechain:
        if newDd.ddType == 'A':
            newDd = newDd.dechain()
        else:
            print("Cannot dechain of type %s to ADD" % newDd.ddType)
    if outfile is not None:
        newDd.writeDd(outfile)
    if aigfile is not None:
        g = newDd.add2aig()
        g.comment("Generated from file %s" % iname)
        g.generate(aigfile)
    if itegfile is not None:
        g = newDd.add2iteg()
        g.comment("Generated from file %s" % iname)
        g.generate(itegfile)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
            
        
        
