import Cli

import ProofChecker.Cat

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let cnfFname := p.positionalArg! "cnf"
  let cratFname := p.positionalArg! "crat"
  try
    let cnf ← CnfForm.readDimacsFile cnfFname.value
    let pf ← CatStep.readDimacsFile cratFname.value
    CheckerState.check cnf pf.toList (traces := p.hasFlag "verbose")
    IO.println "PROOF SUCCESSFUL"
    return 0
  catch e =>
    IO.println s!"PROOF FAILED\n{e}"
    return 1

def checkCmd : Cli.Cmd := `[Cli|
  CheckCRAT VIA runCheckCmd; ["0.0.1"]
  "Check a CRAT proof."

  FLAGS:
    v, verbose;          "Print diagnostic information."

  ARGS:
    cnf  : String;      "The CNF input file."
    crat : String;      "The CRAT proof file."

  EXTENSIONS:
    Cli.author "Wojciech Nawrocki"
]

def main (args : List String) : IO UInt32 := do
  checkCmd.validate args