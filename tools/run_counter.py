#!/usr/bin/python3

# Run model counting program on benchmark file

import getopt
import sys
import subprocess
import datetime

def usage(name):
    print("Usage: %s [-h] [-H HPATH] FILE.cnf ..." % name)
    print("  -h       Print this message")
    print("  -H HPATH Specify pathname for directory")

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

timeLimits = { "D4" : 60, "GEN" : 300, "HINT" : 300, "FCHECK" : 60 }

def runProgram(prefix, root, commandList, logFile):
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

def runD4(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cmd = [d4Program, cnfName, "-dDNNF", "-out=" + nnfName]
    return runProgram("D4", root, cmd, logFile)

def runGen(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cratName = home + "/" + root + ".crat"
    cmd = [interp, genProgram, "-d", "-i", cnfName, "-n", nnfName, "-p", cratName, "-H", "2", "-L", "2", "-s", "2"]
    return runProgram("GEN", root, cmd, logFile)

def runHint(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    hcratName = home + "/" + root + ".hcrat"
    cmd = [interp, hintProgram, "-i", cnfName, "-p", cratName, "-o", hcratName, "-s", "2"]
    return runProgram("HINT", root, cmd, logFile)

def runCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    hcratName = home + "/" + root + ".hcrat"
    cmd = [checkProgram, cnfName, hcratName]
    return runProgram("FCHECK", root, cmd, logFile)

def runSequence(root, home):
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    logName = root + ".log"
    try:
        logFile = open(logName, 'w')
    except:
        print("%s. %s ERROR:Couldn't open file '%s'" % (root, prefix, logName))
        return
    ok = False
    if runD4(root, home, logFile):
        if runGen(root, home, logFile):
            if runHint(root, home, logFile):
                if runCheck(root, home, logFile):
                    ok = True
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    outcome = "normal" if ok else "failed"
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    print("%s. %s OUTCOME: %s" % (root, prefix, outcome))
    print("%s. %s Elapsed time: %.3f seconds" % (root, prefix, seconds))
    logFile.write(result)
    logFile.close()

def stripSuffix(fname, expected):
    fields = fname.split(".")
    if fields[-1] == expected:
        fields = fields[:-1]
        return ".".join(fields)
    return None

def runBatch(home, cnfList):
    roots = [stripSuffix(f, "cnf") for f in cnfList]
    roots = [r for r in roots if r is not None]
    print("Running on roots %s" % roots)
    for r in roots:
        runSequence(r, home)

def run(name, args):
    home = "."
    optList, args = getopt.getopt(args, "hH:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-H':
            home = val
        else:
            print("Unknown option '%s'" % opt)
            return
    runBatch(home, args)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

