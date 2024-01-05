#!/usr/bin/python3

## Extract subset of columns from CSV file

import sys
import getopt
import csv


def usage(name):
    print("Usage: %s [-h] C1:C2:...:Ck < INFILE > OUTFILE")
    print("  -h            Print this information")
    print("  C1:C2:...:Ck  Specify subset of columns to include (numbered from 1)")




def process(columnList):
    creader = csv.reader(sys.stdin)
    for fields in creader:
        idx = 0
        nfields = []
        for col in fields:
            idx += 1
            if idx in columnList:
                nfields.append(col)
        line = ",".join(nfields)
        sys.stdout.write(line + "\n")

def run(name, args):
    if len(args) != 1 or args[0] == '-h':
        usage(name)
        return 0
    try:
        fields = args[0].split(':')
        columnList = [int(field) for field in fields]
    except:
        usage(name)
        return 1;
    return process(columnList)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        

        
    
    
