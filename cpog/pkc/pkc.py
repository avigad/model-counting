#!/usr/bin/python3

import sys
import getopt
import datetime

import readwrite
import cnf
import ddnnf
import pog
import project

        
def usage(name):
    print("Usage: %s [-h] [-k] [-v VLEVEL] [-i FILE.cnf] [-p FILE.cpog]")
    print(" -h           Print this message")
    print(" -k           Keep intermediate files")
    print(" -v VLEVEL    Set verbosity level (0-3)")
    print(" -i FILE.cnf  Input CNF")
    print(" -p FILE.cpog Output CPOG")

def run(name, args):
    verbLevel = 1
    d4 = True
    cnfName = None
    pogName = None
    keep = False

    optlist, args = getopt.getopt(args, 'hkdv:i:n:p:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-k':
            keep = True
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-d':
            d4 = True
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            pogName = val
        else:
            print("Invalid option '%s'" % (opt))
            return

    if cnfName is None:
        print("Must give name of CNF file")
        return
    start = datetime.datetime.now()
    creader = readwrite.CnfReader(cnfName, verbLevel, False)
    pcnf = cnf.PackedCnf(creader.nvar)
    pcnf.load(creader.clauses)
    cnf.setRoot(cnfName)
    pog = project.pcnf2ppog(pcnf, creader.showVariables, verbLevel)
    if pogName is not None:
        pog.write(pogName)
        print("GEN: POG file %s written" % pogName)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    rtime = seconds - (cnf.satTime + cnf.d4Time)
    print("GEN: Elapsed time for generation: %.2f seconds" % seconds)
    print("GEN:    Time for SAT:  %.2f seconds" %  cnf.satTime)
    print("GEN:    Time for D4:   %.2f seconds" %  cnf.d4Time)
    print("GEN:    Time for rest: %.2f seconds" %  rtime)
    print("GEN %s" % project.pcache.stats())
    print("GEN: SAT solver calls = %d   D4 calls = %d" % (cnf.satCalls, cnf.d4Calls))
    if not keep:
        cnf.removeFiles()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
