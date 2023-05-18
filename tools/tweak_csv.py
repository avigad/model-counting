#!/usr/bin/python3

# Given column, threshold, and saturation value:
# Set items that exceed threshold to saturation value

import sys
import getopt
import csv

def eprint(s):
    sys.stderr.write(s + '\n')


def usage(name):
    eprint("Usage: %s [-h] -c COL -t THRESH [-v SVAL] -i FILE.csv" % name)
    eprint("  -h            Print this message")
    eprint("  -c COL        Select column")
    eprint("  -t THRESH     Set threshold")
    eprint("  -v SVAL       Set saturation value (otherwise, omit row")
    eprint("  -i FILE       Input file")

# Process a single file, building entries
# Return dictionary of entries + count of number of entries per line
def processFile(fname, col, thresh, sval):
    try:
        infile = sys.stdin if fname is None else open(fname)
        creader = csv.reader(infile)
    except:
        eprint("Couldn't open CSV file '%s'" % fname)
        sys.exit(1)
    for fields in creader:
        fval = None
        keep = True
        if len(fields) >= col:
            try:
                fval = float(fields[col-1])
            except:
                pass
        if fval is not None and fval > thresh:
            if sval is None:
                keep = False
            else:
                fields[col-1] = str(sval)
        if keep:
            print(",".join(fields))
    if fname is not None:
        infile.close()


def run(name, args):
    col = None
    thresh = None
    sval = None
    fname = None
    optList, args = getopt.getopt(args, "hc:t:v:i:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            sys.exit(0)
        elif opt == '-c':
            col = int(val)
        elif opt == '-t':
            thresh = float(val)
        elif opt == '-v':
            sval = float(val)
        elif opt == '-i':
            fname = val
        else:
            eprint("Unknown option '%s'" % opt)
            usage(name)
            sys.exit(1)
    if col is None or thresh is None:
        eprint("Missing argument")
        usage(name)
        return
    processFile(fname, col, thresh, sval)    

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        

        
    
    
