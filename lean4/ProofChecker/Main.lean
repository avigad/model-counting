import Cli

import ProofChecker.Checker.Parse
import ProofChecker.Checker.CheckerCore

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let cnfFname := p.positionalArg! "cnf"
  let cratFname := p.positionalArg! "crat"
  let verbose := p.hasFlag "verbose"
  let count := p.hasFlag "count"
  IO.print "Parsing CNF..\n"
  let (cnf, nVars) ← ICnf.readDimacsFile cnfFname.value
  IO.print "done.\nParsing CRAT..\n"
  (← IO.getStdout).flush
  let pf ← CratStep.readDimacsFile cratFname.value
  IO.print "done.\n"
  if verbose then
    IO.print "Reprinted proof:\n"
    for step in pf do
      IO.println step.toDimacs
  IO.print "Checking proof..\n"
  (← IO.getStdout).flush
  if count then
    match checkProofAndCount cnf nVars pf with
    | .ok v =>
      IO.println "PROOF SUCCESSFUL"
      IO.println s!"Model count: {v}"
      return 0
    | .error e =>
      IO.println s!"PROOF FAILED\n{e}"
      return 1
  else
    match checkProof cnf nVars pf with
    | .ok _ =>
      IO.println "PROOF SUCCESSFUL"
      return 0
    | .error e =>
      IO.println s!"PROOF FAILED\n{e}"
      return 1

def checkCmd : Cli.Cmd := `[Cli|
  CheckCRAT VIA runCheckCmd; ["0.0.3"]
  "Check a CRAT proof."

  FLAGS:
    v, verbose;          "Print diagnostic information."
    c, count;            "Output the unweighted model count."

  ARGS:
    cnf  : String;      "The CNF input file."
    crat : String;      "The CRAT proof file."

  EXTENSIONS:
    Cli.author "Wojciech Nawrocki"
]

def main (args : List String) : IO UInt32 := do
  checkCmd.validate args