#!/usr/bin/python

# Test of DD code

import getopt
import sys
import dd

def usage(name):
    print("Usage: %s [-h] [-c] [-a] [-i IFILE] [-o OFILE] [-A AFILE]")
    print(" -h       Print this message")
    print(" -c       Remove chaining")
    print(" -a       Convert to ADD")
    print(" -i IFILE Input file")
    print(" -o OFILE Output DD file")
    print(" -A AFILE Output AIG file")

def run(name, args):
    dechain = False
    makeAdd = False
    infile = sys.stdin
    outfile = sys.stdout
    aigfile = None

    optlist, args = getopt.getopt(args, "hcai:o:A:")
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
            except:
                print("Couldn't open output AIG file '%s'" % val)
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
        g.generate(aigfile)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
            
        
        
