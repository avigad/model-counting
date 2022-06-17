#!/usr/bin/python

# Model counting for free ITE graph
# Optionally generate output ITEG file

import getopt
import sys
import iteg
import writer

def usage(name):
    print("Usage: %s [-h] [-i IFILE] [-p PREFIX] [-o OFILE] [-q QFILE] [-P PFILE]" % name)
    print(" -h         Print this message")
    print(" -i IFILE   Input ITE graph file")
    print(" -p PREFIX  Prefix for lines of interest")
    print(" -o OFILE   Write ITE graph to file")
    print(" -q QFILE   Write QBF representation of ITE graph to file")
    print(" -P PFILE   Write levelized permutation of QBF variables")
    
def process(iname, prefix, oname, qname, pname):
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
    if oname is not None:
        try:
            ofile = open(oname, 'w')
        except:
            print("Couldn't open output file '%s'" % oname)
            return
        g.generate(ofile)
        ofile.close
    if qname is not None:
        root =  qname
        suffix = 'qcnf'
        fields = qname.split('.')
        if len(fields) > 1:
            root = ".".join(fields[:-1])
            suffix = fields[-1]
        try:
            qwriter = writer.QcnfWriter(root, suffix)
        except Exception as ex:
            print("Couldn't initialize QBF writer '%s'" % str(ex))
            return
        g.genQbf(qwriter)
        qwriter.finish()
    if pname is not None:
        icount = len([n.id for n in g.gates if n.isInput or n.isIte])
        root =  pname
        suffix = 'order'
        fields = pname.split('.')
        if len(fields) > 1:
            root = ".".join(fields[:-1])
            suffix = fields[-1]
        try:
            pwriter = writer.OrderWriter(icount, root, suffix = suffix)
        except Exception as ex:
            print("Couldn't initialize Order writer '%s'" % str(ex))
            return
        g.genOrder(pwriter)
        pwriter.finish()

def run(name, args):
    iname = None
    oname = None
    prefix = None
    qname = None
    pname = None
    optlist, args = getopt.getopt(args, "hi:p:o:q:P:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-i':
            iname = val
        elif opt == '-p':
            prefix = val
        elif opt == '-o':
            oname = val
        elif opt == '-q':
            qname = val
        elif opt == '-P':
            pname = val
        else:
            print("Unknown command option '%s'" % opt)
            return
    process(iname, prefix, oname, qname, pname)
        
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
