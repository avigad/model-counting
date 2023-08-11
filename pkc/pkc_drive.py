#!/usr/bin/python3


#####################################################################################
# Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
# Last edit: May 19, 2022
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

import getopt
import sys
import os.path
import subprocess
import datetime
import time

def usage(name):
    print("Usage: %s [-h] [-f] [-v VERB] [-t TIME] [-l NFILE] [FILE.EXT ...]" % name)
    print("  -h       Print this message")
    print("  -f       Force regeneration of all files")
    print("  -v       Set verbosity level")
    print("  -t TIME  Limit time for each of the programs")
    print("  -l NFILE Specify file containing root names")
    print("  EXT can be any extension for wild-card matching (e.g., cnf, nnf)")

# Defaults
standardTimeLimit = 60

verbLevel = 1
force = False

nameFile = None

# Pathnames
homePath = "/Users/bryant/repos"

genHome = homePath + "/model-counting/pkc"
genProgram = genHome + "/pkc"

timeLimit = 4000

commentChar = 'c'

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def setTimeLimit(t):
    global timeLimit
    timeLimit = t

def runProgram(prefix, root, commandList, logFile, extraLogName = None):
    tlimit = timeLimit
    result = ""
    cstring = " ".join(commandList)
    print("%s. %s: Running '%s' with time limit of %d seconds" % (root, prefix, cstring, tlimit))
    logFile.write("%s LOG: Running %s\n" % (prefix, cstring))
    logFile.write("%s LOG: Time limit %d seconds\n" % (prefix, tlimit))
    start = datetime.datetime.now()
    try:
        cp = subprocess.run(commandList, capture_output = True, timeout=tlimit, text=True)
    except subprocess.TimeoutExpired as ex:
        # Incorporate information recorded by external logging
        if (extraLogName is not None):
            try:
                xlog = open(extraLogName, "r")
                for line in xlog:
                    logFile.write(line)
                xlog.close()
            except:
                pass
        print("%s. %s Program timed out after %d seconds" % (root, prefix, tlimit))
        result += "%s ERROR: Timeout after %d seconds\n" % (prefix, tlimit)
        delta = datetime.datetime.now() - start
        seconds = delta.seconds + 1e-6 * delta.microseconds
        result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
        result += "%s OUTCOME: Timeout\n" % (prefix)
        logFile.write(result)
        return False
    ok = True
    if cp.returncode != 0:
        result += "%s ERROR: Return code = %d\n" % (prefix, cp.returncode)
        ok = False
    outcome = "normal" if ok else "failed"
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    print("%s. %s: OUTCOME: %s" % (root, prefix, outcome))
    print("%s. %s: Elapsed time: %.3f seconds" % (root, prefix, seconds))
    logFile.write(cp.stdout)
    logFile.write(result)
    return ok

def runPkc(root, home):
    cnfName = home + "/" + root + ".cnf"
    logName = home + "/" + root + ".pkc_log"
    extraLogName = "backup.log"
    if not force and os.path.exists(logName):
        print("Already have file '%s'.  Skipping" % logName)
        return True
    cmd = [genProgram]
    cmd += ["-v", str(verbLevel)]
    cmd += ["-L", extraLogName]
    cmd += [cnfName]
    try:
        logFile = open(logName, "w")
    except:
        print("%s ERROR:Couldn't open file '%s'" % (root, logName))
        return
    ok = runProgram("PKC", root, cmd, logFile, extraLogName = extraLogName)
    return ok

def stripSuffix(fname):
    fields = fname.split(".")
    if len(fields) > 1:
        fields = fields[:-1]
    return ".".join(fields)

def runBatch(home, fileList, force):
    roots = [stripSuffix(f) for f in fileList]
    roots = [r for r in roots if r is not None]
    print("Running on roots %s" % roots)
    for r in roots:
        runPkc(r, home)

def run(name, args):
    global verbLevel, force, nameFile
    home = "."
    optList, args = getopt.getopt(args, "hfv:t:l:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        if opt == '-v':
            verbLevel = int(val)
        elif opt == '-f':
            force = True
        elif opt == '-t':
            setTimeLimit(int(val))
        elif opt == '-l':
            nameFile = val
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    fileList = args
    if nameFile is not None:
        try:
            nfile = open(nameFile, 'r')
        except:
            print("Couldn't open name file '%s'" % nameFile)
            usage(name)
            return
        for line in nfile:
            fname = trim(line)
            fileList.append(fname)
        nfile.close
            
    runBatch(home, fileList, force)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)

