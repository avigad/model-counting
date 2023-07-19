#!/usr/bin/python3

import sys
import getopt
import datetime

import readwrite
import ddnnf
import pog
import project

        
def usage(name):
    print("Usage: %s [-h] [-v VLEVEL] [-i FILE.cnf] [-p FILE.cpog]")
    print(" -h           Print this message")
#    print(" -d           Use NNF format defined for D4 model counter")
    print(" -v VLEVEL    Set verbosity level (0-3)")
    print(" -i FILE.cnf  Input CNF")
    print(" -p FILE.cpog Output CPOG")

def run(name, args):
    verbLevel = 1
    d4 = True
    cnfName = None
    pogName = None

    optlist, args = getopt.getopt(args, 'hdv:i:n:p:')
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
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
    pr = project.Projector(cnfName, verbLevel)
    pr.run()
    if pogName is not None:
        pr.write(pogName)
        print("GEN: POG file %s written" % pogName)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    print("GEN: Elapsed time for generation: %.2f seconds" % seconds)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
