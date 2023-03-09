/-! For parsing DIMACS-like formats -/

namespace Dimacs

inductive Token where
  | int (i : Int) | str (s : String)
  deriving Repr, BEq

instance : Coe String Token :=
  ⟨Token.str⟩

instance : Coe Int Token :=
  ⟨Token.int⟩

instance : ToString Token where
  toString := fun | .int v | .str v => toString v

def Token.getInt? : Token → Option Int
  | .int i => some i
  | .str _ => none

def Token.getStr? : Token → Option String
  | .int _ => none
  | .str s => some s

def tokenizeFile (fname : String) : IO (List (List Token)) := do
  let mut lns := #[]
  for ln in (← IO.FS.lines fname) do
    let tks := ln.splitOn " " |>.filter (· ≠ "")
    if tks.isEmpty then continue
    if tks.head! == "c" then continue
    let mut ln := #[]
    for tk in tks do
      if let some i := tk.toInt? then
        ln := ln.push <| .int i
      else
        ln := ln.push <| .str tk
    lns := lns.push ln.toList
  return lns.toList


end Dimacs

def Lit.ofDimacs? (s : String) : Option (Lit String) :=
  if s.isEmpty then none
  else if s.get! 0 == '-' then neg (s.drop 1)
  else pos s

def Clause.ofDimacsLits (tks : List Dimacs.Token) : Except String (Clause Nat) := do
  let lits ← tks.mapM (·.getInt? |> Except.ofOption "expected int" |>.map Lit.ofInt)
  return Clause.mk lits

def CnfForm.readDimacsFile (fname : String) : IO (CnfForm Nat) := do
  let mut cnf := #[]
  let _hdr :: lns ← Dimacs.tokenizeFile fname | throwThe IO.Error s!"missing CNF header"
  for tks in lns do
    let some (.int 0) := tks.getLast? | throwThe IO.Error s!"missing terminating 0"
    let lits := tks.dropLast
    match Clause.ofDimacsLits lits with
    | .ok C => cnf := cnf.push C
    | .error e => throw <| IO.userError e
  return cnf.toList

def Lit.ofInt (i : Int) : Lit Nat :=
  if i < 0 then Lit.neg i.natAbs
  else Lit.pos i.natAbs

open Dimacs in
/-- Makes a step given a DIMACS line. -/
def ofDimacs (tks : List Token) : Except String (CratStep Nat Nat Int) := do
  let toUpHints (tks : List Token) : Except String (Array Nat) := do
    if let [.str "*"] := tks then
      throw s!"got unhinted proof, but all hints need to be filled in"
    List.toArray <$> tks.mapM (·.getInt? |> Except.ofOption "expected int" |>.map Int.natAbs)
  let posInt (x : Int) : Except String Nat := do
    if x < 0 then throw s!"expected positive int {x}"
    return x.natAbs
  let clauseOfLitTks (tks : List Token) : Except String (Array Int) := do
    List.toArray <$> tks.mapM (·.getInt? |> Except.ofOption "expected int")
  match tks with
  | [.int idx, .str "a"] ++ tks =>
    let grps := List.splitOn (.int 0) tks
    let lits :: pf? := grps | throw s!"expected clause in '{grps}'"
    let pf := pf?.head?.getD []
    return .addAt (← posInt idx) (← clauseOfLitTks lits) (← toUpHints pf)
  | [.str "dc", .int idx] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .delAt (← posInt idx) (← toUpHints pf)
  | [.int idx, .str "p", .int v] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let ls ← tks.dropLast.mapM (·.getInt? |> Except.ofOption "expected int")
    if ls.length < 2 then throw s!"expected at least two literals"
    return .prod (← posInt idx) (← posInt v) ls.toArray
  | [.int idx, .str "s", .int v, .int l₁, .int l₂] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .sum (← posInt idx) (← posInt v) l₁ l₂ (← toUpHints pf)
  | [.str "do", .int v] =>
    return .delOp (← posInt v)
  | [_, .str "i"] ++ _ =>
    throw s!"input clause command is deprecated"
  | _ => throw s!"unexpected line"

def readDimacsFile (fname : String) : IO (Array <| CratStep Nat Nat Int) := do
  let mut pf := #[]
  for ln in (← Dimacs.tokenizeFile fname) do
    match CratStep.ofDimacs ln with
    | .ok s => pf := pf.push s
    | .error e => throw <| IO.userError s!"failed to parse line '{ln}': {e}"
  return pf
