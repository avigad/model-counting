#!/usr/bin/python3

# Run cd4 certifying ddnnf compiler

import getopt
import sys
import os.path
import subprocess
import datetime
import time

def usage(name):
    print("Usage: %s [-h] [-f] [-t TIME] FILE.EXT ..." % name)
    print("  -h       Print this message")
    print("  -f       Force regeneration of all files")
    print("  -t TIME  Limit time for all programs")
    print("  EXT      Can be any extension for wild-card matching (e.g., cnf, nnf)")

# Defaults
standardTimeLimit = 1000

# Pathnames
homePath = "/Users/bryant/repos"
d4Path = homePath + "/d4"
d4Program = d4Path + "/d4"
checkProgram = d4Path + "/certificator"
dratPath = homePath + "/drat-trim"
dtrimProgram = dratPath + "/drat-trim"

timeLimits = { "D4" : 4000, "DTRIM" : 4000, "CHECK" : 4000 }

commentChar = 'c'

def setTimeLimit(t):
    global timeLimits, standardTimeLimit
    standardTimeLimt = min(standardTimeLimit, t)
    for k in timeLimits.keys():
        timeLimits[k] = min(timeLimits[k], t)

def checkFile(prefix, fname, logFile):
    f = open(fname, 'r')
    bytes = 0
    lines = 0
    for line in f:
        if len(line) > 0 and line[0] == commentChar:
            continue
        bytes += len(line)
        lines += 1
    print("%s LOG: size %s %d lines %d bytes" % (prefix, fname, lines, bytes))
    logFile.write("%s LOG: size %s %d lines %d bytes\n" % (prefix, fname, lines, bytes))
    f.close()

def runProgram(prefix, root, commandList, logFile, returnCodes = None):
    if returnCodes is None:
        returnCodes = [0]
    if prefix in timeLimits:
        timeLimit = timeLimits[prefix]
    else:
        timeLimit = standardTimeLimit
    result = ""
    cstring = " ".join(commandList)
    print("%s. %s: Running '%s' with time limit of %d seconds" % (root, prefix, cstring, timeLimit))
    logFile.write("%s LOG: Running %s\n" % (prefix, cstring))
    logFile.write("%s LOG: Time limit %d seconds\n" % (prefix, timeLimit))
    start = datetime.datetime.now()
    try:
        cp = subprocess.run(commandList, capture_output = True, timeout=timeLimit, text=True)
    except subprocess.TimeoutExpired as ex:
        print("%s. %s Program timed out after %d seconds" % (root, prefix, timeLimit))
        result += "%s ERROR: Timeout after %d seconds\n" % (prefix, timeLimit)
        delta = datetime.datetime.now() - start
        seconds = delta.seconds + 1e-6 * delta.microseconds
        result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
        result += "%s OUTCOME: Timeout\n" % (prefix)
        logFile.write(result)
        return False
    ok = True

    if cp.returncode not in returnCodes:
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

# Only run D4 if don't yet have .nnf file
def runD4(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".cnnf"
    dratName = home + "/" + root + ".drat"
    cmd = [d4Program, cnfName, "-dDNNF", "-out=" + nnfName, "-drat=" + dratName]
    ok = runProgram("D4", root, cmd, logFile)
    if ok:
        checkFile(root + ". D4 NNF", nnfName, logFile)
        checkFile(root + ". D4 DRAT", dratName, logFile)
    if not ok and os.path.exists(nnfName):
        os.remove(nnfName)
    return ok

def runDtrim(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    dratName = home + "/" + root + ".drat"
    cmd = [dtrimProgram, cnfName, dratName, "-f", "-U"]
    ok = runProgram("DTRIM", root, cmd, logFile, returnCodes = [0,1])
    return ok    

def runCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".cnnf"
    dratName = home + "/" + root + ".drat"
    cmd = [checkProgram, cnfName, nnfName, dratName]
    ok =  runProgram("CHECK", root, cmd, logFile)
    return ok


def runSequence(root, home, force):
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    extension = "cd4_log"
    logName = root + "." + extension
    if not force and os.path.exists(logName):
            print("Already have file %s.  Skipping benchmark" % logName)
            return
    try:
        logFile = open(logName, 'w')
    except:
        print("%s. %s ERROR:Couldn't open file '%s'" % (root, prefix, logName))
        return
    ok = False
    done = False
    ok = runD4(root, home, logFile)
    if ok:
        ok = ok and runDtrim(root, home, logFile)
    if ok:
        ok = ok and runCheck(root, home, logFile)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    outcome = "normal" if ok else "failed"
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    print("%s. %s OUTCOME: %s" % (root, prefix, outcome))
    print("%s. %s Elapsed time: %.3f seconds" % (root, prefix, seconds))
    print("%s. %s Logfile at %s" % (root, prefix, logName))
    logFile.write(result)
    logFile.close()

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
        runSequence(r, home, force)

def run(name, args):
    home = "."
    force = False
    optList, args = getopt.getopt(args, "hft:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-f':
            force = True
        elif opt == '-t':
            setTimeLimit(int(val))
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    runBatch(home, args, force)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)

