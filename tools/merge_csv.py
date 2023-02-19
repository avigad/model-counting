#!/usr/bin/python3

## Merge set of CSV file into single file with headings
## Each source file must have lines of form key,value
## The files must all have the keys in the same order
## The keys for the first entry must be a superset of the rest.

## Optionally filter out keys for which one more fields is empty

import sys
import getopt
import csv

def eprint(s):
    sys.stderr.write(s + '\n')


def usage(name):
    eprint("Usage: %s [-h] [-f] [-l L0,L1,L2,...,Ln] FILE1.csv FILE2.csv ... FILEn.csv" % name)
    eprint("  -f            Filter out lines that have at least one field missing")
    eprint("  -h            Print this message")
    eprint("  -l LABELS     Provide comma-separated set of heading labels")
    eprint("  FILE1.csv ... Source files")

# List of keys in order first encountered
keys = []
# Growing list of result lines
lines = []
# Set of keys with missing entries
missingKeys = set([])

def addData(fname, first = False):
    global keys, lines, missingKeys
    try:
        infile = open(fname)
        creader = csv.reader(infile)
    except:
        eprint("Coudn't open CSV file '%s'" % fname)
        sys.exit(1)
    row = 0
    for fields in creader:
        row += 1
        if len(fields) != 2:
            eprint("Error in file %s, row %d.  Can only handle CSV files with two items per row" % (fname, row))
            sys.exit(1)
        key = fields[0]
        val = fields[1]
        if first:
            keys.append(key)
            lines.append(key + "," + val)
        else:
            if row > len(keys):
                eprint("File %s, row %d.  Too many entries" % (fname, row))
                sys.exit(1)
            while row <= len(keys) and keys[row-1] != key:
                missingKeys.add(keys[row-1])
                lines[row-1] += ","
                row += 1
            if row > len(keys):
                eprint("File %s, row %d.  Couldn't find key '%s'" % (fname, row, key))
                sys.exit(1)                
            lines[row-1] += "," + val
    while row <= len(lines):
        lines[row-1] += ","
        missingKeys.add(keys[row-1])
        row += 1
    infile.close()
        

def filter():
    global keys, lines
    okeys = keys
    olines = lines
    keys = []
    lines = []
    for (key,line) in zip(okeys, olines):
        if key not in missingKeys:
            keys.append(key)
            lines.append(line)
    
def build(lstring, flist, doFilter):
    global lines
    first = True
    for fname in flist:
        addData(fname, first)
        first = False
    if doFilter:
        filter()
    if len(lstring) > 0:
        lines = [lstring] + lines
    for line in lines:
        print(line)

def run(name, args):
    doFilter = False
    lstring = ""
    optList, args = getopt.getopt(args, "hfl:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            sys.exit(0)
        elif opt == '-f':
            doFilter = True
        elif opt == '-l':
            lstring = val
        else:
            eprint("Unknown option '%s'" % opt)
            usage(name)
            sys.exit(1)
    build(lstring, args, doFilter)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        

        
    
    
