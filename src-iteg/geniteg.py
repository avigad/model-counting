#!/usr/bin/python

# Generate certified canonical ITEG from QBF formula

# Process.  Given input.qcnf:
# 1. Run QBF solver to generate canonical BDD representation.
#    This is represented as formula bdd.qcnf with an embedded ITEG
# 2. Run proof checker to certify solver result
# 3. Extract the embedded ITEG.  That will be the final output
# 4. Generate a QBF from ITEG.
# 5. Run solver again.  It should generate file syntactically equal to bdd.qcnf
# 6. Run proof checker to certify solver result

# Programs called:
# Solver: bddgen.py
# Prover: cchecker.py
# ITEG extractor: miteg.py

import getopt
import os
import subprocess
import sys

import util

def usage(name):
    print("Usage: %s -h -v VERB -k -i input.qcnf -o output.iteg -P VPERM -L logfile")
    print("  -h             Print this message")
    print("  -v VERB        Set verbosity level of programs called")
    print("  -k             Keep intermediate files.  These all have names based on input file name")
    print("  -i input.qcnf  Input formula")
    print("  -o output.iteg Output representation")
    print("  -P VPERM       Specify permutation of variables for BDD ordering")
    print("       Should have free variables numbered numbered starting at 1 and in that relative order in permutation")
    print("  -L logfile     Write output to specified log file")

logger = None

programDirectory = None

programs = {
    'solver' : "bddgen.py",
    'checker' : "cchecker.py",
    'extractor' : "miteg.py"
}

def getProgram(name):
    if name not in programs:
        logger.write("Internal Error.  No program named '%s'\n" % name)
        sys.exit(1)
    return programDirectory + '/' + programs[name]

def buildFile(nameFile, rest):
    root = nameFile
    fields = nameFile.split('.')
    if len(fields) > 1:
        root = ".".join(fields[:-1])
    return root + rest


def runCode(fields):
    cmd = " ".join(fields)
    ok = True
    logger.write("Running '%s'\n" % cmd)
    p = subprocess.Popen(fields, stdout=subprocess.PIPE, stderr = subprocess.PIPE)
    out, err = p.communicate()
    if p.returncode != 0:
        logger.write("ERROR.  %s exited with return code %d\n" % (fields[0], p.returncode))
        ok = False
    logger.write(out)
    logger.write(err)
    return ok


def checkFiles(fname1, fname2):
    try:
        f1 = open(fname1, 'r')
    except:
        logger.write("Couldn't open file %s\n" % fname1)
        return False
    try:
        f2 = open(fname2, 'r')
    except:
        logger.write("Couldn't open file %s\n" % fname2)
        return False

    lines1 = f1.readlines()
    lines2 = f2.readlines()

    l1 = 0
    l2 = 0
    len1 = len(lines1)
    len2 = len(lines2)
    ok = True
    while l1 < len1 and l2 < len2:
        # Get non-comment line
        while lines1[l1][0] == 'c' and l1 < len1:
            l1 += 1
        while lines2[l2][0] == 'c' and l2 < len2:
            l2 += 1
        if l1 < len1 and l2 < len2:
            if lines1[l1] == lines2[l2]:
                l1+= 1
                l2+= 1
                continue
            else:
                logger.write("Mismatch.  %s, line #%d (%s) != %s, line #%d (%s)\n" % (fname1, l1+1, lines1[l1], fname2, l2+1, lines2[l2]))
                ok = False
                break
        elif l1 < len1:
            logger.write("Mismatch.  %s, line #%d (%s) != %s reached end of file\n" % (fname1, l1+1, lines1[l1], fname2))
            ok = False
            break
        elif l2 < len2:
            logger.write("Mismatch.  %s reached end of file. %s, line #%d (%s)\n" % (fname1, fname2, l2+1, lines2[l2]))
            ok = False
            break
    f1.close()
    f2.close()
    if ok:
        logger.write("Files %s and %s match.\n" % (fname1, fname2))
    return ok

def runSolver(inQbf, outQbf, outProof, perm, verbLevel):
    fields = [getProgram('solver'), '-v', str(verbLevel), '-i', inQbf, '-o', outQbf, '-p', outProof]
    if perm is not None:
        fields += ['-P', perm]
    return runCode(fields)
        
def runChecker(inQbf, inProof, genQbf, verbLevel):
    fields = [getProgram('checker')]
    if verbLevel > 1:
        fields += ['-v']
    fields += ['-i', inQbf, '-c', genQbf, '-p', inProof]
    return runCode(fields)

def runExtractor(inQbf, outIteg, outQbf, perm):
    fields = [getProgram('extractor'), '-i', inQbf, '-p', 'c_ITEG', '-o', outIteg, '-q', outQbf]
    if perm is not None:
        fields += ['-P', perm]
    return runCode(fields)

def run(name, args):
    global logger
    keepFiles = False
    vlevel = 0
    inQbf = None
    outIteg = None
    perm = None
    logName = None
    optlist, args = getopt.getopt(args, "hv:ki:o:P:L:")
    for opt, val in optlist:
        if opt == '-h':
            usage(name)
            return True
        elif opt == '-v':
            vlevel = int(val)
        elif opt == '-k':
            keepFiles = True
        elif opt == '-i':
            inQbf = val
        elif opt == '-o':
            outIteg = val
        elif opt == '-P':
            perm = val
        elif opt == '-L':
            logName = val

    if inQbf is None:
        print("Must have input QBF")
        return False

    if outIteg is None:
        print("Must have output ITEG")
        return False

    try:
        logger = util.Logger(logName)
    except:
        print("Couldn't open log file '%s'" % logName)
        return

    genQbf = buildFile(inQbf, "-bdd.qcnf")
    outProof = buildFile(inQbf, "-bdd.qproof")
    logger.write("Generating BDD from input formula\n")
    if not runSolver(inQbf, genQbf, outProof, perm, vlevel):
        logger.write("Exiting\n")
        return
    logger.write("Checking proof\n")
    if not runChecker(inQbf, outProof, genQbf, vlevel):
        logger.write("Exiting\n")
        return

    logger.write("Generating ITEG\n")
    itegQbf = buildFile(inQbf, "-iteg.qcnf")
    itegOrder = buildFile(inQbf, "-iteg.order")
    if not runExtractor(genQbf, outIteg, itegQbf, itegOrder):
        logger.write("Exiting\n")
        return

    logger.write("Generating BDD from ITEG\n")
    checkQbf = buildFile(inQbf, "-iteg-check.qcnf")
    checkProof = buildFile(inQbf, "-iteg-check.qproof")
    if not runSolver(itegQbf, checkQbf, checkProof, itegOrder, vlevel):
        logger.write("Exiting\n")
        return

    logger.write("Checking proof\n")
    if not runChecker(itegQbf, checkProof, checkQbf, vlevel):
        logger.write("Exiting\n")
        return

    logger.write("Comparing files\n")
    if not checkFiles(genQbf, checkQbf):
        logger.write("Exiting\n")
        return

    if not keepFiles:
        xfiles = [genQbf, outProof, itegQbf, itegOrder, checkQbf, checkProof]
        for fname in xfiles:
            try:
                os.remove(fname)
            except:
                logger.write("Couldn't delete file '%s'\n")
                continue
            if vlevel > 1:
                logger.write("Deleted file '%s'\n" % fname)
    logger.write("All tests PASS\n")


if __name__ == "__main__":
    programName = os.path.realpath(__file__)
    fields = programName.split('/')
    programDirectory = "/".join(fields[:-1])
    run (sys.argv[0], sys.argv[1:])
