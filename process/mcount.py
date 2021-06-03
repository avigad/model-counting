#!/usr/bin/python

# Model counting for free ITE graph

import getopt
import sys
import iteg

def usage(name):
    print("Usage: %s [-h] [-i IFILE] [-p PREFIX]" % name)
    print(" -h         Print this message")
    print(" -i IFILE   Input ITE graph file")
    print(" -p PREFIX  Prefix for lines of interest")
    
def process(iname, prefix):
    if iname is None:
        ifile = sys.stdin
    else:
        try:
            ifile = open(iname, 'r')
        except:
            print("Couldn't open input file '%s'" % iname)
            return
    g0 = iteg.IteGraph(0)
    try:
        g = g0.load(ifile, prefix = prefix)
    except iteg.ParseException as ex:
        print("Failed to read input file: %s" % str(ex))
        return
    for onode in g.outputs:
        count = g.countModels(onode)
        print("Output node %d.  Models: %d" % (onode.id, count))
    if ifile != sys.stdin:
        ifile.close()

def run(name, args):
    iname = None
    prefix = None
    optlist, args = getopt.getopt(args, "hi:p:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-i':
            iname = val
        elif opt == '-p':
            prefix = val
        else:
            print("Unknown command option '%s'" % opt)
            return
    process(iname, prefix)
        
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
