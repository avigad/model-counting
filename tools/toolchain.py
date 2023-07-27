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
    print("Usage: %s [-h] [-1] [-2] [-f] [-v VERB] [-s n|g] [-m (m|s|h)] [-p] [-L] [-G] [-F] [-t TIME] [-l NFILE] [FILE.EXT ...]" % name)
    print("  -h       Print this message")
    print("  -f       Force regeneration of all files")
    print("  -v       Set verbosity level")
    print("  -s n|g   Stop after NNF generation or CPOG generation (g)")
    print("  -1       Generate one-sided proof (don't validate assertions)")
    print("  -2       Use D4 version 2")
    print("  -m m|s|h Generation mode: monolithic (m), structured (s), or hybrid (h)")
    print("  -p       Preprocess (within D4).  Should then use monolithic mode for CPOG generation")
    print("  -L       Expand each node, rather than using lemmas")
    print("  -G       Prove each literal separately, rather than grouping into single proof")
    print("  -F       Run Lean checker to formally check")
    print("  -t TIME  Limit time for each of the programs")
    print("  -l NFILE Specify file containing root names")
    print("  EXT      Can be any extension for wild-card matching (e.g., cnf, nnf)")

# Blocking file.  If present in directory, won't proceed.  Recheck every sleepTime seconds
blockPath = "./block.txt"
sleepTime = 60

# Defaults
standardTimeLimit = 60

verbLevel = 1
oneSided = False
monolithic_threshold = 1000 * 1000
tree_ratio_threshold = 5.0
mode = 'h'
preprocess = False
useLemma = True
group = True
useLean = False
d4v2 = False

nameFile = None

# Pathnames
homePath = "/Users/bryant/repos"
d4Path = homePath + "/d4"
d4Program = d4Path + "/d4"
d4v2Path = homePath + "/d4v2"
d4v2Program = d4v2Path + "/d4"

genHome = homePath + "/model-counting/cpog/generator"
genProgram = genHome + "/cpog-generate"

checkHome = homePath + "/model-counting/cpog/checker"
checkProgram = checkHome + "/cpog-check"

leanHome = homePath + "/model-counting/lean4"
leanCheckProgram = leanHome + "/ProofChecker/build/bin/checker"

#timeLimits = { "D4" : 4000, "GEN" : 1000, "FCHECK" : 1000, "LCHECK" : 1000 }
timeLimits = { "D4" : 4000, "GEN" : 10000, "FCHECK" : 10000, "LCHECK" : 10000}

clauseLimit = (1 << 31) - 1

commentChar = 'c'

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def setTimeLimit(t):
    global timeLimits
    for key in timeLimits.keys():
        if t < timeLimits[key]:
            timeLimits[key] = t

def waitWhileBlocked():
    first = True
    while os.path.exists(blockPath):
        if first:
            print("Waiting to unblock")
        first = False
        time.sleep(sleepTime)

def checkFile(prefix, fname, logFile):
    f = open(fname, 'r')
    bytes = 0
    lines = 0
    for line in f:
        if len(line) > 0 and line[0] == commentChar:
            continue
        bytes += len(line)
        lines += 1
    print("%s: LOG: size %s %d lines %d bytes" % (prefix, fname, lines, bytes))
    logFile.write("%s: LOG: size %s %d lines %d bytes\n" % (prefix, fname, lines, bytes))
    f.close()

def runProgram(prefix, root, commandList, logFile, extraLogName = None):
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
        # Incorporate information recorded by external logging
        if (extraLogName is not None):
            try:
                xlog = open(extraLogName, "r")
                for line in xlog:
                    logFile.write(line)
                xlog.close()
            except:
                pass
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

def nnfNamer(root, home):
    if preprocess:
        return home + "/" + root + "pre.nnf"
    else:
        return home + "/" + root + ".nnf"

# Only run D4 if don't yet have .nnf file
def runD4(root, home, logFile, force):
    cnfName = home + "/" + root + ".cnf"
    nnfName = nnfNamer(root, home)
    if not force and os.path.exists(nnfName):
        return True

    if d4v2:
        cmd = [d4v2Program, "-i", cnfName, "-m", "ddnnf-compiler", "--dump-ddnnf", nnfName]
    else:
        cmd = [d4Program, cnfName, "-dDNNF", "-out=" + nnfName]
        if preprocess:
            cmd += ["-preproc=backbone+vivification+occElimination"]
    ok = runProgram("D4", root, cmd, logFile)
    if ok:
        checkFile(root + ". D4 NNF", nnfName, logFile)
    if not ok and os.path.exists(nnfName):
        os.remove(nnfName)
    return ok

def runPartialGen(root, home, logFile, force):
    cnfName = home + "/" + root + ".cnf"
    nnfName = nnfNamer(root, home)
    cpogName = home + "/" + root + ".cpog"
    cmd = [genProgram, "-v", str(verbLevel), "-p", cnfName, nnfName, cpogName]
    ok = runProgram("GEN", root, cmd, logFile)
    if not ok and os.path.exists(cpogName):
        os.remove(cpogName)
    return ok


def runGen(root, home, logFile, force):
    global monolithic_threshold, tree_ratio_threshold
    if mode == 'm':
        monolithic_threshold = -1
        tree_ratio_threshold = 1e12
    elif mode == 's':
        monolithic_threshold = 0
        tree_ratio_threshold = 0
    extraLogName = "d2p.log"
    cnfName = home + "/" + root + ".cnf"
    nnfName = nnfNamer(root, home)
    cpogName = home + "/" + root + ".cpog"
#    if not force and os.path.exists(cpogName):
#        return True
    cmd = [genProgram]
    cmd += ["-v", str(verbLevel)]
    if oneSided:
        cmd += ['-1']
    cmd += ['-m', str(monolithic_threshold), '-r', str(tree_ratio_threshold)]
    if not useLemma:
        cmd += ['-e']
    if not group:
        cmd += ['-s']
    cmd += ["-C", str(clauseLimit), "-L", extraLogName, cnfName, nnfName, cpogName]
    ok = runProgram("GEN", root, cmd, logFile, extraLogName = extraLogName)
    if ok:
        checkFile(root + ". GEN", cpogName, logFile)
    if not ok and os.path.exists(cpogName):
        os.remove(cpogName)
    return ok

def runCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cpogName = home + "/" + root + ".cpog"
    cmd = [checkProgram]
    cmd += ["-v", str(verbLevel)]
    if oneSided:
        cmd += ['-1']
    cmd += [cnfName, cpogName]
    ok =  runProgram("FCHECK", root, cmd, logFile)
    return ok

def runLeanCheck(root, home, logFile):
    cnfName = home + "/" + root + ".cnf"
    cpogName = home + "/" + root + ".cpog"
    cmd = [leanCheckProgram]
    cmd += [cnfName, cpogName]
    ok =  runProgram("LCHECK", root, cmd, logFile)
    return ok


def runSequence(root, home, stopD4, stopGen, force):
    waitWhileBlocked()
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    extension = "log"
    if oneSided:
        extension = "onesided_" + extension
    prefix = "mono" if mode == 'm' else "structured" if mode == 's' else "hybrid"
    extension = prefix + "_" + extension
    if preprocess:
        extension = "preprocess_" + extension
    if not useLemma:
        extension = "nolemma_" + extension
    if not group:
        extension = "split_" + extension
    if useLean:
        extension = "lean_" + extension
    if stopD4:
        extension = "D4_log"
    if stopGen:
        extension = "d2p_" + extension
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
    ok = runD4(root, home, logFile, force)
    if stopD4:
        ok = ok and runPartialGen(root, home, logFile, force)
        done = True
    if not done:
        ok = ok and runGen(root, home, logFile, force)
    done = done or stopGen
    if useLean:
        if not done:
            ok = ok and runLeanCheck(root, home, logFile)
    else:
        if not done:
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


def runBatch(home, fileList, stopD4, stopGen, force):
    roots = [stripSuffix(f) for f in fileList]
    roots = [r for r in roots if r is not None]
    print("Running on roots %s" % roots)
    for r in roots:
        runSequence(r, home, stopD4, stopGen, force)

def run(name, args):
    global verbLevel, useLemma, group, oneSided, mode, useLean, preprocess, d4v2, nameFile
    home = "."
    stopD4 = False
    stopGen = False
    force = False
    optList, args = getopt.getopt(args, "hfv:12m:pLGFs:t:l:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        if opt == '-v':
            verbLevel = int(val)
        elif opt == '-f':
            force = True
        elif opt == '-1':
            oneSided = True
        elif opt == '-2':
            d4v2 = True
        elif opt == '-m':
            mode = val
            if val not in "hms":
                print("Unknown mode '%s'" % val)
                usage(name)
                return
        elif opt == '-p':
            preprocess = True
        elif opt == '-L':
            useLemma = False
        elif opt == '-G':
            group = False
        elif opt == '-F':
            useLean = True
        elif opt == '-s':
            if val == 'n':
                stopD4 = True
            elif val == 'g':
                stopGen = True
            else:
                print("Unknown stopping condition '%s'" % val)
                usage(name)
                return
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
            
    runBatch(home, fileList, stopD4, stopGen, force)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)

