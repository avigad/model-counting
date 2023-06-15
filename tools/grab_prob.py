#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

import sys
import re

# Generate csv
# with file root in first column
# and number extracted from file name in second

def usage(name):
    print("Usage: %s file ...")

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

# Sequence of one or more digits
inumber = re.compile('[\d]+')

def getRoot(path):
    pieces = path.split("/")
    fname = pieces[-1]
    fields = fname.split(".")
    if len(fields) > 1:
        fields = fields[:-1]
    return ".".join(fields)

# Get number from file name
def getNumber(fname):
    # Try to find size from file name:
    try:
        m = re.search(inumber, fname)
        n = int(m.group(0))
        return m.group(0)
    except:
        print("Couldn't extract problem size from file name '%s'" % fname)
        return None


# Extract clause data from log.  Turn into something useable for other tools
def extract(fname):
    tag = getRoot(fname)
    val = getNumber(fname)
    return (tag, val)

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        usage(name)
        return
    vals = {}
    for fname in args:
        pair = extract(fname)
        if pair is not None:
            if pair[0] in vals:
                vals[pair[0]].append(pair)
            else:
                vals[pair[0]] = [pair]
    for k in sorted(vals.keys()):
        for p in vals[k]:
            print("%s,%s" % p)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
