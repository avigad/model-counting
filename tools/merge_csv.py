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
    eprint("Usage: %s [-h] [-f]  [-s I1:I2:...:Ik] [-r I1:I2] [-l L0,L1,L2,...] FILE1.csv FILE2.csv ... FILEn.csv" % name)
    eprint("  -f            Filter out lines that have at least one field missing")
    eprint("  -s I1:I2:...:Ik Sum the values from specified files 1..n and add as new column")
    eprint("  -r I1:I2      Form the ratio between the values from specified files 1 and 2 and add as new column")
    eprint("  -h            Print this message")
    eprint("  -l LABELS     Provide comma-separated set of heading labels")
    eprint("  FILE1.csv ... Source files")
    eprint("  (If give numeric value, then it gets used for all entries")

# Growing set of result lines, indexed by key
globalEntries = {}
# Number of columns in entries
globalCount = 0

# Process a single file, building entries
# Return dictionary of entries + count of number of entries per line
def processFile(fname):
    entries = {}
    columnCount = 0
    try:
        infile = open(fname)
        creader = csv.reader(infile)
    except:
        eprint("Couldn't open CSV file '%s'" % fname)
        sys.exit(1)
    row = 0
    for fields in creader:
        row += 1
        key = fields[0]
        entry = fields[1:]
        dcount = len(entry)
        if columnCount == 0:
            columnCount = dcount
        elif dcount != columnCount:
            eprintf("File %s, row %d.  Expecting %d entries.  Found %d" % (fname, row, columnCount, dcount))
            sys.exit(1)
        entries[key] = entry
    infile.close()
    return (entries, columnCount)
    
# Merge two sets of entries.
# When they both don't have the same keys, then either form superset or subset
def merge(entries1, count1, entries2, count2, subset = True):
    entries = {}
    for k in entries1.keys():
        entry1 = entries1[k]
        if k in entries2:
            entry2 = entries2[k]
            entries[k] = entry1 + entry2
        elif not subset:
            entry2 = [""] * count2
            entries[k] = entry1 + entry2
    if not subset:
        for k in entries2.keys():
            if k in entries1:
                continue
            entry1 = [""] * count1
            entry2 = entries2[k]
            entries[k] = entry1 + entry2
    return entries
        
def mergeConstant(entries1, value):
    entries = {}
    for k in entries1.keys():
        entry1 = entries1[k]
        entries[k] = entry1 + [str(value)]
    return entries

def nextFile(fname, first, subset):
    global globalEntries, globalCount
    value = None
    try:
        value = int(fname)
    except:
        pass
    if value is not None:
        globalEntries = mergeConstant(globalEntries, value)
        globalCount += 1
        return

    entries, ccount = processFile(fname)
    if first:
        globalEntries = entries
        globalCount = ccount
    else:
        globalEntries = merge(globalEntries, globalCount, entries, ccount, subset)
        globalCount += ccount

def sumEntries(sumList):
    global globalEntries, globalCount
    for k in globalEntries.keys():
        fields = globalEntries[k]
        sfields = [fields[i] for i in range(globalCount) if i+1 in sumList]
        try:
            nums = [float(field) if len(field) > 0 else 0.0 for field in sfields]
        except:
            print("Couldn't sum fields for line with key %s.  Summing over %s" % (k, str(sfields)))
            sys.exit(1)
        sval = sum(nums)
        fields.append(sval)
    globalCount += 1

def divideEntries(ratioList):
    global globalEntries, globalCount
    for k in globalEntries.keys():
        fields = globalEntries[k]
        try:
            sfields = [fields[i-1] for i in ratioList]
        except:
            print("Couldn't get fields %s from line with key %s.  Fields: %s" % (str(ratioList), k, str(fields)))
            sys.exit(1)
        try:
            nums = [float(field) if len(field) > 0 else 0.0 for field in sfields]
        except:
            print("Couldn't divide fields for line with key %s.  Dividing over %s" % (k, str(sfields)))
            sys.exit(1)
        rval = 1000 * 1000.0 if nums[1] == 0 else nums[0]/nums[1]
        fields.append(rval)
    globalCount += 1


def build(lstring, flist, doFilter, sumList, ratioList):
    first = True
    for fname in flist:
        nextFile(fname, first, doFilter)
        first = False
    if sumList is not None:
        sumEntries(sumList)
    if ratioList is not None:
        divideEntries(ratioList)
    if len(lstring) > 0:
        print(lstring)
    for k in sorted(globalEntries.keys()):
        sfields = [k] + [str(field) for field in globalEntries[k]]
        print(",".join(sfields))

def run(name, args):
    doFilter = False
    sumList = None
    ratioList = None
    lstring = ""
    optList, args = getopt.getopt(args, "hfs:r:l:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            sys.exit(0)
        elif opt == '-f':
            doFilter = True
        elif opt == '-s' or opt == '-r':
            fields = val.split(':')
            try:
                ivals = [int(field) for field in fields]
                if opt == '-s':
                    sumList = ivals
                else:
                    ratioList = ivals
                    if len(ratioList) != 2:
                        eprint("Ratio can only be between two elements")
                        usage(name)
                        sys.exit(1)
            except Exception as ex:
                eprint("Couldn't extract column numbers from argument '%s' (%s)" % (val % str(ex)))
                usage(name)
                sys.exit(1)
        elif opt == '-l':
            lstring = val
        else:
            eprint("Unknown option '%s'" % opt)
            usage(name)
            sys.exit(1)
    build(lstring, args, doFilter, sumList, ratioList)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        

        
    
    
