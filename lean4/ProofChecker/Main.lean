import Cli

import ProofChecker.Data.Dimacs
import ProofChecker.Cat

def readDimacsCnf (fname : String) : IO (Array (Array Int)) := do
  let mut cnf := #[]
  let _hdr :: lns ← Dimacs.tokenizeFile fname | throwThe IO.Error s!"missing CNF header"
  let clauseOfLitTks (tks : List Dimacs.Token) : Except String (Array Int) := do
    List.toArray <$> tks.mapM (·.getInt? |> Except.ofOption "expected int")
  for tks in lns do
    let some (.int 0) := tks.getLast? | throwThe IO.Error s!"missing terminating 0"
    let lits := tks.dropLast
    match clauseOfLitTks lits with
    | .ok C => cnf := cnf.push C
    | .error e => throw <| IO.userError e
  return cnf

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let cnfFname := p.positionalArg! "cnf"
  let cratFname := p.positionalArg! "crat"
  try
    IO.print "Parsing CNF.."
    let cnf ← readDimacsCnf cnfFname.value
    IO.print "done.\nParsing CRAT.."
    (← IO.getStdout).flush
    let pf ← CratStep.readDimacsFile cratFname.value
    IO.print "done.\nChecking.."
    (← IO.getStdout).flush
    CheckerState.check cnf pf.toList (verbose := p.hasFlag "verbose")
    IO.println "\nPROOF SUCCESSFUL"
    return 0
  catch e =>
    IO.println s!"\nPROOF FAILED\n{e}"
    return 1

def checkCmd : Cli.Cmd := `[Cli|
  CheckCRAT VIA runCheckCmd; ["0.0.2"]
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