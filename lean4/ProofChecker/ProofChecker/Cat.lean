import Std.Data.HashMap
import Std.Data.RBTree

import ProofChecker.Data.Cnf
import ProofChecker.Data.Dimacs


/-- A step in a CAT proof. Clause indices have type `α` and variables type `ν`.
As a trick, we could set `α := Clause ν` to have direct access to clauses without
going through an index mapping. -/
inductive CatStep (α ν : Type)
  | /-- Add input clause. -/
    addInput (idx : α) (C : Clause ν)
  | /-- Add asymmetric tautology. Empty hints means inferred. -/
    addAt (idx : α) (C : Clause ν) (upHints : List α)
  | /-- Add asymmetric tautology. Empty hints means inferred. -/
    delAt (idx : α) (upHints : List α)
  | /-- Declare product operation. -/
    prod (idx : α) (x : ν) (l₁ l₂ : Lit ν)
  | /-- Declare sum operation. Empty hints means inferred. -/
    sum (idx : α) (x : ν) (l₁ l₂ : Lit ν) (upHints : List α)
  | /-- Delete operation. -/
    delOp (x : ν)
  deriving Repr

namespace CatStep

instance [ToString α] [ToString ν] : ToString (CatStep α ν) where
  toString := fun
    | addInput idx C => s!"{idx} i ({C})"
    | addAt idx C upHints => s!"{idx} a ({C}) (hints: {upHints})"
    | delAt idx upHints => s!"dc {idx} (hints: {upHints})"
    | prod idx x l₁ l₂ => s!"{idx} p {x} {l₁} {l₂}"
    | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} (hints: {upHints})"
    | delOp x => s!"do {x}"

open Dimacs in
/-- Makes a step given a DIMACS line. -/
def ofDimacs (tks : List Token) : Except String (CatStep Nat Nat) := do
  let toUpHints (tks : List Token) : Except String (List Nat) := do
    if let [.str "*"] := tks then return []
    tks.mapM (·.getInt? |> Except.ofOption "expected int" |>.map Int.natAbs)
  let posInt (x : Int) : Except String Nat := do
    if x < 0 then throw s!"expected positive int {x}"
    return x.natAbs
  match tks with
  | .int idx :: .str "i" :: tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let lits := tks.dropLast
    return .addInput (← posInt idx) (← Clause.ofDimacsLits lits)
  | .int idx :: .str "a" :: tks =>
    let grps := List.splitOn (.int 0) tks
    let lits :: pf? := grps | throw s!"expected clause in '{grps}'"
    let pf := pf?.head?.getD []
    return .addAt (← posInt idx) (← Clause.ofDimacsLits lits) (← toUpHints pf)
  | .str "dc" :: .int idx :: tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .delAt (← posInt idx) (← toUpHints pf)
  | [.int idx, .str "p", .int v, .int l₁, .int l₂] =>
    return .prod (← posInt idx) (← posInt v) (Lit.ofInt l₁) (Lit.ofInt l₂)
  | .int idx :: .str "s" :: .int v :: .int l₁ :: .int l₂ :: tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .sum (← posInt idx) (← posInt v) (Lit.ofInt l₁) (Lit.ofInt l₂) (← toUpHints pf)
  | [.str "do", .int v] =>
    return .delOp (← posInt v)
  | tks => throw s!"unexpected line {tks}"

def readDimacsFile (fname : String) : IO (Array <| CatStep Nat Nat) := do
  let mut pf := #[]
  for ln in (← Dimacs.tokenizeFile fname) do
    match CatStep.ofDimacs ln with
    | .ok s => pf := pf.push s
    | .error e => throw <| IO.userError e
  return pf

end CatStep

namespace CountingScheme

-- TODO: under what conditions is a counting scheme an SDD? ROBDD?

/-- Every node in a scheme is a variable of type `ν`, defined as equivalent
to a literal or a combination of variables. -/
inductive Node ν
  /- Extension variable for sum of subdiagrams with disjoint assignments. -/
  | sum (a b : Lit ν)
  /- Extension variable for product of subdiagrams with disjoint dependency sets. -/
  | prod (a b : Lit ν)
  deriving Repr, Inhabited

structure Graph (ν : Type) [BEq ν] [Hashable ν] where
  /--
  `nodes x = y` when x ↔ y, i.e. the node `y` defines the extension variable `x`
  -/
  nodes : Std.HashMap ν (Node ν)

variable {ν : Type} [BEq ν] [Hashable ν]

def Graph.empty : Graph ν := {
  nodes := Std.HashMap.empty }

inductive GraphUpdateError ν where
  | varAlreadyExists (x : ν)
  | unknownVar (x : ν)

instance [ToString ν] : ToString (GraphUpdateError ν) where
  toString := fun
    | .varAlreadyExists x => s!"variable '{x}' already exists"
    | .unknownVar x => s!"unknown extension variable '{x}'"

def Graph.update (g : Graph ν) : CatStep α ν → Except (GraphUpdateError ν) (Graph ν)
  | .prod _ x l₁ l₂ =>
    if g.nodes.contains x then
      throw <| .varAlreadyExists x
    else
      return { g with nodes := g.nodes.insert x <| .prod l₁ l₂ }
  | .sum _ x l₁ l₂ _ =>
    if g.nodes.contains x then
      throw <| .varAlreadyExists x
    else
      return { g with nodes := g.nodes.insert x <| .sum l₁ l₂ }
  | .delOp x =>
    if !g.nodes.contains x then
      throw <| .unknownVar x 
    else
      return { g with nodes := g.nodes.erase x }
  | _ => .ok g

--  A-->|text|B
def Graph.toMermaidChart [ToString ν] (g : Graph ν) : String := Id.run do
  let mut ret := "flowchart TB\n"
  let mkArrowEnd (x : Lit ν) := if x.polarity then s!"{x.var}" else s!"|NOT|{x.var}"
  for (x, node) in g.nodes.toArray do
    match node with
    | .sum a b =>
      ret := ret ++ s!"{x}([{x} OR])\n"
      ret := ret ++ s!"{x} -->{mkArrowEnd a}\n"
      ret := ret ++ s!"{x} -->{mkArrowEnd b}\n"
    | .prod a b =>
      ret := ret ++ s!"{x}({x} AND)\n"
      ret := ret ++ s!"{x} -->{mkArrowEnd a}\n"
      ret := ret ++ s!"{x} -->{mkArrowEnd b}\n"
  return ret

end CountingScheme

structure CheckerState where
  inputCnf : CnfForm Nat := CnfForm.mk []
  originalVars : Nat := inputCnf.maxVar?.getD 0
  clauseDb : Std.HashMap Nat (Clause Nat) := {}
  -- which clauses a given literal occurs in
  occurs : Std.HashMap (Lit Nat) (Array Nat) := {}
  /-- Which variables an extension variable transitively depends on. -/
  -- invariant: extension variable is in `depends` iff it has been introduced
  depends : Std.HashMap Nat (Std.RBTree Nat compare) := {}
  /-- Which extension variables directly depend on a variable. -/
  revDeps : Std.HashMap Nat (Std.RBTree Nat compare) := {}
  /-- The first clause of the three clauses defining an extension variable. -/
  extDefClauses : Std.HashMap Nat Nat := {}
  scheme : CountingScheme.Graph Nat := CountingScheme.Graph.empty
  trace : Array String := #[]

  -- /--
  -- `backrefs x` lists all the vars which directly reference this var.
  -- We use this to implement abstraction / collapse nodes.
  -- -/
  -- backrefs : Std.HashMap ν (Std.HashSet ν)

instance : Inhabited CheckerState := ⟨{}⟩

inductive CheckerError where
  | graphUpdateError (err : CountingScheme.GraphUpdateError Nat)
  | duplicateClauseIdx (idx : Nat)
  | wrongClauseIdx (idx : Nat)
  | hintNotUnit (idx : Nat)
  | upNoContradiction (τ : PropAssignment Nat)
  | varNotExtension (x : Nat)
  | varHasRevDeps (x : Nat)
  | missingHint (idx : Nat) (pivot : Lit Nat)
  | duplicateExtVar (x : Nat)
  | unknownExtVar (x : Nat)
  | sumNotDisjoint (x y : Nat)

namespace CheckerError

instance : ToString CheckerError where
  toString := fun
    | graphUpdateError e => s!"graph update error: {e}"
    | duplicateClauseIdx idx => s!"duplicate clause index: {idx}"
    | wrongClauseIdx idx => s!"wrong clause index: {idx}"
    | hintNotUnit idx => s!"hinted clause at {idx} did not become unit"
    | upNoContradiction τ => s!"unit propagation did not derive contradiction (final assignment {τ})"
    | varNotExtension x => s!"variable '{x}' is not an extension variable"
    | varHasRevDeps x => s!"variable '{x}' cannot be removed as others depend on it"
    | missingHint idx pivot => s!"missing hint for clause {idx} resolved on '{pivot}'"
    | duplicateExtVar x => s!"extension variable '{x}' already introduced"
    | unknownExtVar x => s!"unknown extension variable '{x}'"
    | sumNotDisjoint x y => s!"variables '{x}' and '{y}' have intersecting dependency sets"

end CheckerError

namespace CheckerState

abbrev CheckerM := ExceptT CheckerError <| StateM CheckerState

def withTraces (f : Array String → String) (x : CheckerM Unit) : CheckerM Unit := do
  let prevTrace ← modifyGet fun st => (st.trace, { st with trace := #[] })
  try x
  finally
    modify fun st => { st with trace := prevTrace.push <| f st.trace }

def log (msg : String) : CheckerM Unit := do
  modify fun st => { st with trace := st.trace.push msg }

def addClause (idx : Nat) (C : Clause Nat) : CheckerM Unit := do
  let st ← get
  if st.clauseDb.contains idx then
    throw <| .duplicateClauseIdx idx
  set { st with clauseDb := st.clauseDb.insert idx C }
  log s!"adding ({C})"

def delClause (idx : Nat) : CheckerM Unit := do
  let st ← get
  if !st.clauseDb.contains idx then
    throw <| .wrongClauseIdx idx
  set { st with clauseDb := st.clauseDb.erase idx }
  log s!"deleting ({st.clauseDb.find! idx})"

def getClause (idx : Nat) : CheckerM (Clause Nat) := do
  let st ← get
  match st.clauseDb.find? idx with
  | none => throw <| .wrongClauseIdx idx
  | some C => return C

/-- Reduce clause at `idx` under `τ`. Return `none` if it reduced to true. -/
def reduceClause (idx : Nat) (τ : PropAssignment Nat) : CheckerM (Option (Clause Nat)) := do
  let C ← getClause idx
  return τ.reduceClause C

-- d₁ d₂ are the vars x depends on
def addExtVar (x : Nat) (d₁ d₂ : Nat) (ensureDisjoint := false) : CheckerM Unit := do
  let st ← get
  if st.depends.contains x then
    throw <| .duplicateExtVar x

  let depsOf (x : Nat) :=
    match st.depends.find? x with
    | some ds => pure ds
    | none =>
      if x > st.originalVars then
        throw <| .unknownExtVar x
      else
      -- TODO introduce these at the start and maintain invariant that `st.depends`
      -- contains all depsets of all present variables
        pure <| Std.RBTree.ofList [x]

  let depends₁ ← depsOf d₁
  let depends₂ ← depsOf d₂

  -- TODO HashSet instead of RBTree?
  if ensureDisjoint ∧ depends₁.any (depends₂.contains ·) then
    throw <| .sumNotDisjoint d₁ d₂
  let allDeps := depends₂.fold (init := depends₁) fun acc x => acc.insert x
    |>.insert d₁ |>.insert d₂

  let revDeps₁ := st.revDeps.find? d₁ |>.getD {} |>.insert x
  let revDeps₂ := st.revDeps.find? d₂ |>.getD {} |>.insert x
  set { st with
    depends := st.depends.insert x allDeps
    revDeps := st.revDeps.insert d₁ revDeps₁ |>.insert d₂ revDeps₂
  }

def delExtVar (x : Nat) : CheckerM Unit := do
  let st ← get
  if x ≤ st.originalVars then
    throw <| .varNotExtension x
  if !(st.revDeps.find? x |>.getD {} |>.isEmpty) then
    throw <| .varHasRevDeps x
  set { st with
    depends := st.depends.erase x
    revDeps := st.revDeps.erase x
  }

/-- Propagate units starting from the given assignment. The clauses in `hints` are expected to become
unit in the order provided, as seen in LRAT. Return the extended assignment, or `none` if a contradiction was found. -/
def propagateWithHints (τ : PropAssignment Nat) (hints : List Nat) : CheckerM (Option (PropAssignment Nat)) := do
  let mut τ := τ
  for hint in hints do
    let some C' ← reduceClause hint τ | throw <| .hintNotUnit hint
    if C'.isEmpty then return none
    let some l := C'.unit? | throw <| .hintNotUnit hint
    τ := τ.extend l
  return some τ

def checkAtWithHints (C : Clause Nat) (hints : List Nat) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithHints notC hints | do
    log s!"({C}) implied by UP"
    return
  throw <| .upNoContradiction τ

/-- Check that `C` is either implied by UP, or is a RAT on its first literal, the *pivot*.
For CRAT we also ensure that the pivot is an extension variable.
`posHints` and `negHints` are as in LRAT -/
def checkRat (C : Clause Nat) (posHints : List Nat) (negHints : List (Nat × List Nat)) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithHints notC posHints | do
    log s!"({C}) implied by UP"
    return /- contradiction found, implied by UP -/
  let some pivot := C.firstLit? | throw <| .upNoContradiction τ
  let st ← get
  if pivot.var ≤ st.originalVars then throw <| .varNotExtension pivot.var
  let negHints := negHints.foldl (init := Std.HashMap.empty) fun acc (i, hs) => acc.insert i hs
  -- TODO this would be much more efficient if we only looped over clauses containing the pivot
  st.clauseDb.forM fun i Ci => do
    if !Ci.contains pivot.negate then return
    for lit in C do
      -- resolvent is a tautology
      if lit ≠ pivot ∧ Ci.contains lit.negate then return
    let some hs := negHints.find? i | throw <| .missingHint i pivot
    let τ' := τ ++ PropAssignment.mk (Ci.filterMap fun x => if x ≠ pivot then some x.negate else none)
    if let some τ' ← propagateWithHints τ' hs then
      throw <| .upNoContradiction τ'
  log s!"({C}) RAT on {pivot}"

partial def propagateWithoutHints (τ : PropAssignment Nat) : CheckerM (Option (PropAssignment Nat)) := do
  -- awfully inefficient UP implementation
  let τ' ← (← get).clauseDb.foldM (init := some τ) fun τ _ Ci => do
    let some τ := τ | return none
    match τ.reduceClause Ci with
    | none => return some τ
    | some [] => return none
    | some [l] => return some (τ.extend l)
    | some _ => return some τ
  match τ' with
  | none => return none
  | some τ' =>
    if τ' == τ then return τ
    else propagateWithoutHints τ'

def checkAtWithoutHints (C : Clause Nat) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithoutHints notC | do
    log s!"({C}) implied by UP"
    return
  throw <| .upNoContradiction τ

def checkRatWithoutHints (C : Clause Nat) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithoutHints notC | do
    log s!"({C}) implied by UP"
    return
  let some pivot := C.firstLit? | throw <| .upNoContradiction τ
  let st ← get
  if pivot.var ≤ st.originalVars then throw <| .varNotExtension pivot.var
  st.clauseDb.forM fun _ Ci => do
    if !Ci.contains pivot.negate then return
    for lit in C do
      if lit ≠ pivot ∧ Ci.contains lit.negate then return
    let τ' := τ ++ PropAssignment.mk (Ci.filterMap fun x => if x ≠ pivot then some x.negate else none)
    if let some τ' ← propagateWithoutHints τ' then
      throw <| .upNoContradiction τ'
  log s!"({C}) RAT on {pivot}"

def updateGraph (step : CatStep Nat Nat) : CheckerM Unit := do
  let st ← get
  match st.scheme.update step with
  | .ok g => set { st with scheme := g }
  | .error e => throw <| .graphUpdateError e

-- TODO check and use hints
def update (step : CatStep Nat Nat) : CheckerM Unit :=
  withTraces (fun ts => s!"{step}:\n\t" ++ ("\n\t".intercalate ts.toList)) do
    match step with
    | .addInput idx C =>
      -- TODO check that it belongs to input CNF, and that all of input CNF is introduced
      addClause idx C
    | .addAt idx C pf =>
      if !pf.isEmpty then checkAtWithHints C pf
      else checkAtWithoutHints C
      addClause idx C
    | .delAt idx pf =>
      let C ← getClause idx
      -- The clause must be AT by everything except itself.
      delClause idx
      if !pf.isEmpty then checkAtWithHints C pf
      else checkAtWithoutHints C
    | step@(.prod idx x l₁ l₂) =>
      addExtVar x l₁.var l₂.var (ensureDisjoint := true)
      let lx := Lit.ofInt x
      addClause idx (Clause.mk [lx, -l₁, -l₂])
      addClause (idx+1) (Clause.mk [-lx, l₁])
      addClause (idx+2) (Clause.mk [-lx, l₂])
      modify fun st => { st with extDefClauses := st.extDefClauses.insert x idx }
      updateGraph step
    | step@(.sum idx x l₁ l₂ pf) =>
      let C := Clause.mk [l₁.negate, l₂.negate]
      if !pf.isEmpty then checkAtWithHints C pf
      else checkAtWithoutHints C
      addExtVar x l₁.var l₂.var
      let lx := Lit.ofInt x
      addClause idx (Clause.mk [-lx, l₁, l₂])
      addClause (idx+1) (Clause.mk [lx, -l₁])
      addClause (idx+2) (Clause.mk [lx, -l₂])
      modify fun st => { st with extDefClauses := st.extDefClauses.insert x idx }
      updateGraph step
    | .delOp x =>
      match (← get).extDefClauses.find? x with
      | none => throw <| .unknownExtVar x
      | some idx =>
        delExtVar x
        delClause idx
        delClause (idx+1)
        delClause (idx+2)
        modify fun st => { st with extDefClauses := st.extDefClauses.erase x }
        updateGraph step

def check (cnf : CnfForm Nat) (pf : List (CatStep Nat Nat)) : IO Bool := do
  let mut st : CheckerState := { inputCnf := cnf }
  for step in pf do
    match update step |>.run.run st with
    | (.error e, _) =>
      IO.println s!"\n\t{e}\n\tclauses: {st.clauseDb.toList}"
      return false
    | (.ok _, st') => st := st'
  return true

def checkWithTraces (cnf : CnfForm Nat) (pf : List (CatStep Nat Nat)) : IO Bool := do
  let mut st : CheckerState := { inputCnf := cnf }
  for step in pf do
    match update step |>.run.run st with
    | (.error e, st') =>
      for t in st'.trace do
        IO.println t
      IO.println s!"\n\t{e}\n\tclauses: {st.clauseDb.toList}"
      return false
    | (.ok _, st') => st := st'
  for t in st.trace do
    IO.println t
  return true

end CheckerState
