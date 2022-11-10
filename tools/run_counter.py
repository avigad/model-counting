#!/usr/bin/python3

# Run model counting program on benchmark file

import getopt
import sys
import subprocess
import datetime

def usage(name):
    print("Usage: %s [-h] [-H HPATH] [-t TLIM] FILE.cnf ..." % name)
    print("  -h       Print this message")
    print("  -H HPATH Specify pathname for directory")
    print("  -t TLIM  Specify timeout limit")

# Defaults
standardTimeLimit = 60

# Pathnames
homePath = "/Users/bryant/repos"
d4Path = homePath + "/d4"
d4Program = d4Path + "/d4"

interp = "/usr/local/bin/python3"
genHome = homePath + "/model-counting/crat/prototype"
genProgram = genHome + "/ddnnf.py"
hintProgram = genHome + "/hintify.py"

checkHome = homePath + "/model-counting/crat/checker"
checkProgram = checkHome + "/crat-check"

def runProgram(prefix, commandList, timeLimit, logFile):
    result = ""
    cstring = " ".join(commandList)
    print("%s: Running '%s' with time limit of %d seconds" % (prefix, cstring, timeLimit))
    logFile.write("%s LOG: Running %s\n" % (prefix, cstring))
    logFile.write("%s LOG: Time limit %d seconds\n" % (prefix, timeLimit))
    start = datetime.datetime.now()
    try:
        cp = subprocess.run(commandList, capture_output = True, timeout=timeLimit, text=True)
    except subprocess.TimeoutExpired as ex:
        print("%s Program timed out after %d seconds" % (prefix, timeLimit))
        result += "%s ERROR: Timeout after %d seconds\n" % (prefix, timeLimit)
        delta = datetime.datetime.now() - start
        seconds = delta.seconds + 1e-6 * delta.microseconds
        result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
        result += "%s OUTCOME: Timeout\n" % (prefix)
        logFile.write(result)
        logFile.close()
        return False
    if cp.returncode != 0:
        result += "%s ERROR: Return code = %d\n" % (prefix, cp.returncode)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    result += "%s OUTCOME: Normal\n" % (prefix)
    print("%s Elapsed time: %.3f seconds" % (prefix, seconds))
    logFile.write(cp.stdout)
    logFile.write(result)
    return True

def runD4(root, home, timeLimit, logFile):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cmd = [d4Program, cnfName, "-dDNNF", "-out=" + nnfName]
    return runProgram("D4", cmd, timeLimit, logFile)

def runGen(root, home, timeLimit, logFile):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cratName = home + "/" + root + ".crat"
    cmd = [interp, genProgram, "-d", "-i", cnfName, "-n", nnfName, "-p", cratName, "-H", "2", "-L", "2", "-s", "2"]
    return runProgram("GEN", cmd, timeLimit, logFile)

def runHint(root, home, timeLimit, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    hcratName = home + "/" + root + ".hcrat"
    cmd = [interp, hintProgram, "-i", cnfName, "-p", cratName, "-o", hcratName, "-s", "2"]
    return runProgram("HINT", cmd, timeLimit, logFile)

def runCheck(root, home, timeLimit, logFile):
    cnfName = home + "/" + root + ".cnf"
    hcratName = home + "/" + root + ".hcrat"
    cmd = [checkProgram, cnfName, hcratName]
    return runProgram("FCHECK", cmd, timeLimit, logFile)

def runSequence(root, home, timeLimit):
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    logName = root + ".log"
    try:
        logFile = open(logName, 'w')
    except:
        print("Couldn't open file '%s'" % logName)
        return
    ok = False
    if runD4(root, home, timeLimit, logFile):
        if runGen(root, home, timeLimit, logFile):
            if runHint(root, home, timeLimit, logFile):
                if runCheck(root, home, timeLimit, logFile):
                    ok = True
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    outcome = "normal" if ok else "failed"
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    print("%s Elapsed time: %.3f seconds" % (prefix, seconds))
    logFile.write(result)
    logFile.close()

def stripSuffix(fname, expected):
    fields = fname.split(".")
    if fields[-1] == expected:
        fields = fields[:-1]
        return ".".join(fields)
    return None

def runBatch(home, cnfList, timeLimit):
    roots = [stripSuffix(f, "cnf") for f in cnfList]
    roots = [r for r in roots if r is not None]
    print("Running on roots %s" % roots)
    for r in roots:
        runSequence(r, home, timeLimit)

def run(name, args):
    timeLimit = standardTimeLimit
    home = "."
    optList, args = getopt.getopt(args, "hH:t:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-H':
            home = val
        elif opt == '-t':
            timeLimit = int(val)
        else:
            print("Unknown option '%s'" % opt)
            return
    runBatch(home, args, timeLimit)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

