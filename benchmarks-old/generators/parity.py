#!/usr/bin/python

# Generate BDD representations of odd parity

import sys
import circuit

def gen(n, fname):
    ckt = circuit.Circuit()
    ckt.comment("Parity of %d variables" % n)
    x = ckt.nameVec("x", n)
    ckt.declare(x)
    out = ckt.node("out")
    ckt.xorN(out, x)
    ckt.store(out, fname)

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        print("Usage: %s N [FILE.bdd]" % name)
        return
    try:
        n = int(args[0])
    except:
        print("Invalid number '%s'" % args[0])
        return
    if len(args) > 1:
        fname = args[1]
    else:
        fname = "parity-%.3d.bdd" % n
    gen(n, fname)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
