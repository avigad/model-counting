#!/usr/bin/python3

## Merge set of CSV file into single file with headings
## Each source file must have lines of form key,value
## The files must all have the same keys in the same order

import sys
import getopt
import csv


def usage(name):
    print("Usage: %s [-h] [-l L0,L1,L2,...,Ln] FILE1.csv FILE2.csv ... FILEn.csv" % name)
    print("  -h            Print this message")
    print("  -l LABELS     Provide comma-separated set of heading labels")
    print("  FILE1.csv ... Source files")

# List of keys in order first encountered
keys = []
# Growing list of result lines
lines = []

def addData(fname, first = False):
    global keys, lines
    try:
        infile = open(fname)
        creader = csv.reader(infile)
    except:
        print("Coudn't open CSV file '%s'" % fname)
        sys.exit(1)
    row = 0
    for fields in creader:
        row += 1
        if len(fields) != 2:
            print("Error in file %s, row %d.  Can only handle CSV files with two items per row" % (fname, row))
            sys.exit(1)
        key = fields[0]
        val = fields[1]
        if first:
            keys.append(key)
            lines.append(key + "," + val)
        else:
            if row > len(keys):
                print("File %s, row %d.  Too many entries" % (fname, row))
                sys.exit(1)
            if keys[row-1] != key:
                print("File %d, row %d.  Expecting key '%s'.  Got '%s'." % (fname, row, keys[row-1], key))
                sys.exit(1)
            lines[row-1] += "," + val
    infile.close()
        
def build(lstring, flist):
    global lines
    first = True
    for fname in flist:
        addData(fname, first)
        first = False
    if len(lstring) > 0:
        lines = [lstring] + lines
    for line in lines:
        print(line)

def run(name, args):
    lstring = ""
    optList, args = getopt.getopt(args, "hl:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            sys.exit(0)
        elif opt == '-l':
            lstring = val
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            sys.exit(1)
    build(lstring, args)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        

        
    
    
