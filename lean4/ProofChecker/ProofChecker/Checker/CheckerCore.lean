import Std.Data.Array.Basic

import ProofChecker.Data.ClauseDb
import ProofChecker.Data.PropGraph
import ProofChecker.Data.HashSet

/-- A step in a CRAT proof. -/
inductive CratStep
  | /-- Add asymmetric tautology. -/
    addAt (idx : Nat) (C : IClause) (upHints : Array Nat)
  | /-- Delete asymmetric tautology. -/
    delAt (idx : Nat) (upHints : Array Nat)
  | /-- Declare product operation. -/
    prod (idx : Nat) (x : Nat) (ls : Array ILit)
  | /-- Declare sum operation. -/
    sum (idx : Nat) (x : Nat) (l₁ l₂ : ILit) (upHints : Array Nat)
  | /-- Declare POG root. -/
    root (r : Nat)

namespace CratStep

instance : ToString CratStep where
  toString := fun
    | addAt idx C upHints => s!"{idx} a {C} 0 (hints : {upHints})"
    | delAt idx upHints => s!"dc {idx} (hints: {upHints})"
    | prod idx x ls => s!"{idx} p {x} {ls}"
    | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} (hints: {upHints})"
    | root x => s!"r {x}"
  
-- TODO : toDimacs

end CratStep

/-- The checker's runtime state. Contains exactly the data needed to fully check a proof. -/
structure CheckerStateCore where
  inputCnf : ICnf
  /-- Number of variables in the original CNF. -/
  numOrigVars : Nat
  /-- The clause database. -/
  clauseDb : ClauseDb Nat := {}
  /-- The dependency set of every variable currently present in the ClauseDb. -/
  depVars : HashMap Nat (HashSet Nat) := {}
  -- TODO: replace with ItegCount?
  -- TODO: should the initial state include all original variables as disconnected verts?
  scheme : PropDag Nat := .empty
  /-- Which clauses are counting scheme definition clauses. -/
  schemeDefs : HashSet Nat := .empty Nat
  root : Option Nat := none

inductive CheckerError where
  | graphUpdateError (err : Dag.DagException Nat)
  | duplicateClauseIdx (idx : Nat)
  | unknownClauseIdx (idx : Nat)
  | hintNotUnit (idx : Nat)
  | hintNonexistent (idx : Nat)
  | upNoContradiction (τ : PartPropAssignment)
  | duplicateExtVar (x : Nat)
  | unknownVar (x : Nat)
  | depsNotDisjoint (xs : List Nat)
  | finalRootNotSet
  | finalClauseInvalid (idx : Nat) (C : IClause)

namespace CheckerError

instance : ToString CheckerError where
  toString := fun
    | graphUpdateError e => s!"graph update error: {e}"
    | duplicateClauseIdx idx => s!"duplicate clause index: {idx}"
    | unknownClauseIdx idx => s!"unknown clause index: {idx}"
    | hintNotUnit idx => s!"hinted clause at {idx} did not become unit"
    | hintNonexistent idx => s!"hinted clause at {idx} does not exist"
    | upNoContradiction τ => s!"unit propagation did not derive contradiction (final assignment {τ.toList})"
    | duplicateExtVar x => s!"extension variable '{x}' was already introduced"
    | unknownVar x => s!"unknown variable '{x}'"
    | depsNotDisjoint xs => s!"variables {xs} have non-disjoint dependency sets"
    | finalRootNotSet => s!"proof done but root variable was not set"
    | finalClauseInvalid idx C => s!"proof done but clause '{C}' at {idx} is neither the root nor a PDAG definition"

end CheckerError

abbrev CheckerCoreM := ExceptT CheckerError <| StateM CheckerStateCore

def initial (inputCnf : ICnf) : CheckerStateCore :=
  { inputCnf
    numOrigVars := inputCnf.vars.size
    clauseDb :=
      let (db, _) := inputCnf.foldl (init := (.empty, 1))
        fun (db, idx) C => (db.addClause idx C, idx + 1)
      db
    depVars := inputCnf.vars.fold (init := .empty) fun s x => s.insert x (.empty Nat)
    scheme := inputCnf.vars.fold (init := .empty) fun s x => s.addVar x |>.toOption.get!
  }

/-- Check if `C` is an asymmetric tautology wrt the clause database. -/
def checkAtWithHints (C : IClause) (hints : Array Nat) : CheckerCoreM Unit := do
  let st ← get
  match st.clauseDb.unitPropWithHints C.toFalsifyingAssignment hints with
  | .contradiction => return ()
  | .extended τ => throw <| .upNoContradiction τ
  | .hintNotUnit hint => throw <| .hintNotUnit hint
  | .hintNonexistent hint => throw <| .hintNotUnit hint

-- NOTE: I'll likely have to rewrite uses of monadic sequencing into functional code because
-- sequencing is non-dependent.

def addClause (idx : Nat) (C : IClause) : CheckerCoreM Unit := do
  let st ← get
  if st.clauseDb.contains idx then
    throw <| .duplicateClauseIdx idx
  set { st with clauseDb := st.clauseDb.addClause idx C }

def saveSchemeDef (idx : Nat) : CheckerCoreM Unit := do
  let st ← get
  set { st with schemeDefs := st.schemeDefs.insert idx }

def addAt (idx : Nat) (C : IClause) (hints : Array Nat) : CheckerCoreM Unit := do
  checkAtWithHints C hints
  addClause idx C

def delAt (idx : Nat) (hints : Array Nat) : CheckerCoreM Unit := do
  let st ← get
  let some C := st.clauseDb.getClause idx
    | throw <| .unknownClauseIdx idx
  set { st with clauseDb := st.clauseDb.delClause idx }
  -- The clause is AT by everything except itself.
  checkAtWithHints C hints

def addProd (idx : Nat) (x : Nat) (ls : Array ILit) : CheckerCoreM Unit := do
  let st ← get

  -- Check that added variable is fresh.
  if st.depVars.contains x then
    throw <| .duplicateExtVar x

  -- Check that variables are known and compute their dependencies.
  let Ds ← ls.mapM fun l =>
    match st.depVars.find? l.var with
    | some D => pure D
    | none => throw <| .unknownVar l.var

  -- Compute total dependency set and check pairwise disjointness.
  let (union, disjoint) := HashSet.Union' Ds
  if !disjoint then
    throw <| .depsNotDisjoint (ls.toList.map ILit.var)

  -- Defining clauses for the conjunction.
  addClause idx (ls.map (-·) |>.push (.mkPos x))
  saveSchemeDef idx
  let _ ← ls.mapIdxM fun i l => do
    addClause (idx+1+i) #[.mkNeg x, l]
    saveSchemeDef (idx+1+i)

  modify fun st => { st with
    depVars := st.depVars.insert x union
    scheme := st.scheme.addConj x (ls.toList.map fun l => (l.polarity, l.var)) |>.toOption.get!
  }

def addSum (idx : Nat) (x : Nat) (l₁ l₂ : ILit) (hints : Array Nat) : CheckerCoreM Unit := do
  let st ← get

  -- Check that added variable is fresh.
  if st.depVars.contains x then
    throw <| .duplicateExtVar x

  -- Check that variables are known and compute their dependencies.
  let some D₁ := st.depVars.find? l₁.var
    | throw <| .unknownVar l₁.var
  let some D₂ := st.depVars.find? l₂.var
    | throw <| .unknownVar l₂.var

  -- Check that variables are mutually exclusive.
  checkAtWithHints #[l₁.neg, l₂.neg] hints

  -- Defining clauses for the disjunction.
  addClause idx     #[.mkNeg x, l₁, l₂]
  saveSchemeDef idx
  addClause (idx+1) #[.mkPos x, -l₁]
  saveSchemeDef (idx+1)
  addClause (idx+2) #[.mkPos x, -l₂]
  saveSchemeDef (idx+2)

  modify fun st => { st with
    depVars := st.depVars.insert x (D₁.union D₂)
    scheme := st.scheme.addDisj x ([(l₁.polarity, l₁.var), (l₂.polarity, l₂.var)]) |>.toOption.get!
  }

def setRoot (r : Nat) : CheckerCoreM Unit := do
  modify fun st => { st with root := some r }

def checkFinalState : CheckerCoreM Unit := do
  let st ← get

  let some r := st.root
    | throw <| .finalRootNotSet

  let _ ← st.clauseDb.foldM (init := ()) fun _ idx C => do
    if C != #[.mkPos r] && !st.schemeDefs.contains idx then
      throw <| .finalClauseInvalid idx C

def checkProofStep (step : CratStep) : CheckerCoreM Unit :=
  match step with
  | .addAt idx C hints => addAt idx C hints
  | .delAt idx hints => delAt idx hints
  | .prod idx x ls => addProd idx x ls
  | .sum idx x l₁ l₂ hints => addSum idx x l₁ l₂ hints
  | .root r => setRoot r

-- def count (r : Nat) : CheckerCoreM Nat := do
--   let st ← get
--   st.scheme.count r st.numOrigVars

def checkProof (cnf : ICnf) (pf : Array CratStep) : Except CheckerError Unit := do
  let mut st : CheckerStateCore := initial cnf
  let x : CheckerCoreM Unit := do
    for step in pf do
      checkProofStep step
    checkFinalState
  let (ret, _) := x.run st |>.run
  ret

-- For relating the scheme defining clauses to the the actual scheme
def schemeDefsToPropTerm : CheckerCoreM (PropTerm Nat) := do
  let st ← get
  return st.schemeDefs.fold (init := .tr) (fun acc idx =>
    let C := st.clauseDb.getClause idx |>.getD #[]
    acc.conj C.toPropTerm)

/-- The given checker state is well-formed. -/
structure CheckerStateWF (st : CheckerStateCore) : Prop where
  -- fresh variables
  -- ∀ x : Nat, x ∈ st.clauseDb.toPropTerm.depVars → st.depVars.contains x
  -- corollary: if not in depVars then does not influence func and can be used as extension var

  -- logical equivalence
  -- let X0 := st.inputCnf.toPropForm.vars
  -- equivalentOver X0 st.inputCnf.toPropForm st.clauseDb.toPropForm
  -- hasUniqueExtension X0 st.clauseDb.toPropForm.vars st.clauseDb.toPropForm

  -- compatibility between clauses and schema
  -- ∀ x : Nat, equivalentOver X0 (.conj x st.schemaToPropForm) (st.scheme.toPropForm x)

  -- decomposability
  -- ∀ x : Nat, st.scheme.toPropForm x |>.decomposable

#exit

-- TODO: re-add tracing in a way compatible with WF-subtyping

/-- Wraps a well-formed checker state with extra stuff for actually running and debugging it. -/
structure CheckerState where
  core : CheckerStateCore
  wf : CheckerStateWF core
  verbose : Bool := false
  trace : Array String := #[]

namespace CheckerState

-- Problem: functions like addClause temporarily break invariants, so can't live in CheckerWFM
-- Solution (?): write CheckerWFM and a lift from CheckerM that takes a proof of the invariants
-- being preserved

abbrev CheckerM := ExceptT CheckerError <| StateM CheckerState

def withTraces (f : Array String → String) (x : CheckerM Unit) : CheckerM Unit := do
  if (← get).verbose then
    let prevTrace ← modifyGet fun st => (st.trace, { st with trace := #[] })
    try x
    finally
      modify fun st => { st with trace := prevTrace.push <| f st.trace }
  else
    x

def log_ (msg : Unit → String) : CheckerM Unit := do
  modify fun st =>
    if st.verbose then { st with trace := st.trace.push <| msg () }
    else st

syntax "log! " interpolatedStr(term) : term
macro_rules
  | `(log! $interpStr) => `(log_ fun _ => s!$interpStr)

end CheckerState