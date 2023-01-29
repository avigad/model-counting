#!/usr/bin/python3

# Run model counting program on benchmark file
# Use newer versions of programs

import getopt
import sys
import os.path
import subprocess
import datetime

def usage(name):
    print("Usage: %s [-h] [-f] [-s n|g|c] [-H HPATH] FILE.cnf ..." % name)
    print("  -h       Print this message")
    printf(" -f       Force regeneration of all files")
    print("  -s n|g|c Stop after NNF generation, CRAT generation (g) or proof check (c)")
    print("  -H HPATH Specify pathname for directory")

# Defaults
standardTimeLimit = 60

# Pathnames
homePath = "/Users/bryant/repos"
d4Path = homePath + "/d4"
d4Program = d4Path + "/d4"

genHome = homePath + "/model-counting/crat/ddnnf2pog"
genProgram = genHome + "/d2p"

checkHome = homePath + "/model-counting/crat/checker"
checkProgram = checkHome + "/crat-check"

interpreter = "python3"
countHome = homePath + "/model-counting/crat/prototype"
countProgram = countHome + "/crat_counter.py"

timeLimits = { "D4" : 300, "GEN" : 600, "FCHECK" : 200, "COUNT" : 300 }

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

# Only run D4 if don't yet have .nnf file
def runD4(root, home, logFile, force):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    if not force and os.path.exists(nnfName):
        return True
    cmd = [d4Program, cnfName, "-dDNNF", "-out=" + nnfName]
    ok = runProgram("D4", root, cmd, logFile)
    if not ok and os.path.exists(nnfName):
        os.remove(nnfName)
    return ok

def runGen(root, home, logFile, force):
    cnfName = home + "/" + root + ".cnf"
    nnfName = home + "/" + root + ".nnf"
    cratName = home + "/" + root + ".crat"
    if not force and os.path.exists(cratName):
        return True
    cmd = [genProgram, "-r", cnfName, nnfName, cratName]
    ok = runProgram("GEN", root, cmd, logFile)
    if not ok and os.path.exists(cratName):
        os.remove(cratName)
    return ok

def runCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    cmd = [checkProgram, cnfName, cratName]
    ok =  runProgram("FCHECK", root, cmd, logFile)
    return ok

def runCount(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cratName = home + "/" + root + ".crat"
    cmd = [interpreter, countProgram, "-i", cnfName, "-p", cratName]
    ok = runProgram("COUNT", root, cmd, logFile)
    return ok

def runSequence(root, home, stopD4, stopGen, stopCheck, force):
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    if stopD4:
        logName = root + ".D4_log"
    elif stopGen:
        logName = root + ".d2p_log"
    else:
        logName = root + ".log"
    try:
        logFile = open(logName, 'w')
    except:
        print("%s. %s ERROR:Couldn't open file '%s'" % (root, prefix, logName))
        return
    ok = False
    done = False
    ok = runD4(root, home, logFile, force)
    done = stopD4
    if not done:
        ok = ok and runGen(root, home, logFile, force)
    done = done or stopGen
    if not done:
        ok = ok and runCheck(root, home, logFile)
    done = done or stopCheck
    if not done:
        ok = ok and runCount(root, home, logFile)
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

def runBatch(home, cnfList, stopD4, stopGen, stopCheck, force):
    roots = [stripSuffix(f, "cnf") for f in cnfList]
    roots = [r for r in roots if r is not None]
    print("Running on roots %s" % roots)
    for r in roots:
        runSequence(r, home, stopD4, stopGen, stopCheck, force)

def run(name, args):
    home = "."
    stopD4 = False
    stopGen = False
    stopCheck = False
    force = False
    optList, args = getopt.getopt(args, "hfH:s:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-f':
            force = True
        elif opt == '-s':
            if val == 'n':
                stopD4 = True
            elif val == 'g':
                stopGen = True
            elif val == 'c':
                stopCheck = True
            else:
                print("Unknown stopping condition '%s'" % val)
                usage(name)
                return
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    runBatch(home, args, stopD4, stopGen, stopCheck, force)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)

