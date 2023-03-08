import Std.Data.Array.Basic

import ProofChecker.Data.ClauseDb
import ProofChecker.Data.Pog
import ProofChecker.Data.HashSet
import ProofChecker.Model.Crat

/-- An index into the `ClauseDb`. -/
abbrev ClauseIdx := Nat

/-- A step in a CRAT proof. -/
inductive CratStep
  | /-- Add asymmetric tautology. -/
    addAt (idx : ClauseIdx) (C : IClause) (upHints : Array ClauseIdx)
  | /-- Delete asymmetric tautology. -/
    delAt (idx : ClauseIdx) (upHints : Array ClauseIdx)
  | /-- Declare product operation. -/
    prod (idx : ClauseIdx) (x : Var) (ls : Array ILit)
  | /-- Declare sum operation. -/
    sum (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (upHints : Array ClauseIdx)
  | /-- Declare POG root. -/
    root (r : ILit)

namespace CratStep

instance : ToString CratStep where
  toString := fun
    | addAt idx C upHints => s!"{idx} a {C} 0 (hints: {upHints})"
    | delAt idx upHints => s!"dc {idx} (hints: {upHints})"
    | prod idx x ls => s!"{idx} p {x} {ls}"
    | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} (hints: {upHints})"
    | root x => s!"r {x}"

end CratStep

inductive CheckerError where
  | graphUpdateError (err : PogError)
  | duplicateClauseIdx (idx : ClauseIdx)
  | unknownClauseIdx (idx : ClauseIdx)
  | hintNotUnit (idx : ClauseIdx) (C : IClause) (σ : PartPropAssignment)
  | upNoContradiction (τ : PartPropAssignment)
  | duplicateExtVar (x : Var)
  | unknownVar (x : Var)
  | depsNotDisjoint (xs : List Var)
  | finalRootNotSet
  | finalClauseInvalid (idx : ClauseIdx) (C : IClause)

namespace CheckerError

instance : ToString CheckerError where
  toString := fun
    | graphUpdateError e => s!"graph update error: {e}"
    | duplicateClauseIdx idx => s!"cannot add clause at index {idx}, index is already used"
    | unknownClauseIdx idx => s!"there is no clause at index {idx}"
    | hintNotUnit idx C σ =>
      s!"hinted clause {C} at index {idx} did not become unit under assignment {σ}"
    | upNoContradiction τ =>
      s!"unit propagation did not derive contradiction (final assignment {τ})"
    | duplicateExtVar x => s!"extension variable {x} was already introduced"
    | unknownVar x => s!"unknown variable {x}"
    | depsNotDisjoint xs => s!"variables {xs} have non-disjoint dependency sets"
    | finalRootNotSet => s!"proof done but root literal was not asserted"
    | finalClauseInvalid idx C =>
      s!"proof done but clause {C} at index {idx} is neither the asserted root nor a PDAG definition"

end CheckerError

/-- The checker's runtime state. Contains exactly the data needed to fully check a proof. -/
structure CheckerStateData where
  inputCnf : ICnf
  /-- The variables present in the original CNF. -/
  -- TODO: not used at the moment; its cardinality is needed to output an absolute model-count,
  -- and also to state invariants; but for the latter, ghost state would suffice
  origVars : HashSet Var
  /-- The clause database. -/
  clauseDb : ClauseDb ClauseIdx
  /-- Maps any variable present in `clauseDb` to the set of all *original* variables it depends on.
  For example, an original `x` is mapped to `{x}` whereas an extension `p` with `p ↔ x ∧ y` is
  mapped to `{x, y}`.

  Variables not present in `clauseDb` are not present in this map. Thus we maintain the invariant
  that a variable is in the `clauseDb` iff it is in the domain of this map. -/
  depVars : HashMap Var (HashSet Var)
  /-- The partitioned-operation graph. -/
  pog : Pog
  /-- Which clauses are POG definition clauses. -/
  pogDefs : HashSet ClauseIdx
  /-- The POG root literal, if we already saw a `root` instruction. Otherwise `none`. -/
  root : Option ILit
  
def CheckerStateData.pogDefs' (st : CheckerStateData) : Set ClauseIdx :=
  { idx | st.pogDefs.contains idx }

noncomputable def CheckerStateData.pogDefsTerm (st : CheckerStateData) : PropTerm Var :=
  st.clauseDb.toPropTermSub st.pogDefs'

def CheckerStateData.origVars' (st : CheckerStateData) : Set Var :=
  { x | st.inputCnf.vars.contains x }

noncomputable def CheckerStateData.origSemVars (st : CheckerStateData) : Finset Var :=
  st.inputCnf.toPropTerm.semVars

open PropTerm in
/-- The given checker state is well-formed. -/
structure CheckerStateWF (st : CheckerStateData) : Prop where
  /- Clause DB invariants. -/

  /-- The input CNF is equivalent to the clause database over original variables. -/
  equivalent_clauseDb : equivalentOver st.origSemVars st.inputCnf.toPropTerm st.clauseDb.toPropTerm
  
  contains_pogDefs : ∀ idx : ClauseIdx, idx ∈ st.pogDefs' → st.clauseDb.contains idx

  /-- POG defining clauses extend uniquely from the original variables to their current set
  of variables. -/
  uep_pogDefs : hasUniqueExtension st.origSemVars st.pogDefsTerm.semVars st.pogDefsTerm
  
  /- Reasoning about variables. -/

  /-- `depVars` contains all variables that influence the clause database. Contrapositive:
  if a variable is not in `depVars` then it does not influence the clause database so can be
  defined as an extension variable. -/
  clauseDb_depVars : ∀ x : Var, x ∈ st.clauseDb.toPropTerm.semVars → st.depVars.contains x

  /-- Variable dependencies are correctly stored in `depVars`. -/
  depVars_pog : ∀ (x : Var) (D : HashSet Var), st.depVars.find? x = some D →
    ∀ y, y ∈ (st.pog.toPropForm (.mkPos x)).vars ↔ D.contains y

  /-- Every formula in the POG forest lives over the original variables. -/
  vars_orig : ∀ x : Var, st.depVars.contains x →
    -- TODO: This formulation is awkward but `⊆ st.origSemVars` is actually just false
    -- Maybe `HashSet.foFinset` would mildly clean this up
    ↑(st.pog.toPropForm (.mkPos x)).vars ⊆ st.origVars'
  
  /- POG invariants. -/

  /-- Every formula in the POG forest is decomposable. For literals not defining anything in the
  forest this still holds by fiat because `st.scheme.toPropForm l = l.toPropForm`. -/
  decomposable_lits : ∀ l : ILit, (st.pog.toPropForm l).decomposable
    
  /- Connecting invariant. -/

  /-- In the context of the POG defining clauses, every variable is s-equivalent to what it defines
  in the POG forest. -/
  -- TODO: need `st.depVars.contains x` as precondition?
  equivalent_lits : ∀ l : ILit, equivalentOver st.origSemVars
    (l.toPropTerm ⊓ st.pogDefsTerm)
    ⟦st.pog.toPropForm l⟧

def CheckerState := { st : CheckerStateData // CheckerStateWF st }

abbrev CheckerM := ExceptT CheckerError <| StateM CheckerState

def initialPog (inputCnf : ICnf) :
    Except CheckerError { p : Pog // ∀ l, p.toPropForm l = l.toPropForm } := do
  inputCnf.vars.foldM (init := ⟨Pog.empty, Pog.toPropForm_empty⟩) fun ⟨acc, hAcc⟩ x =>
    match h : acc.addVar x with
    | .ok g => pure ⟨g, by
      intro l
      by_cases hEq : x = l.var
      . rw [hEq] at h
        exact acc.toPropForm_addVar_lit _ _ h
      . rw [acc.toPropForm_addVar_lit_of_ne _ _ _ h hEq]
        apply hAcc⟩
    | .error e => throw <| .graphUpdateError e

def initial (inputCnf : ICnf) : Except CheckerError CheckerState := do
  let ⟨initPog, hInitPog⟩ ← initialPog inputCnf
  let st := {
    inputCnf
    origVars := inputCnf.vars
    clauseDb := .ofICnf inputCnf
    depVars := inputCnf.vars.fold (init := .empty) fun s x =>
      s.insert x (HashSet.empty Var |>.insert x)
    pog := initPog
    pogDefs := .empty ClauseIdx
    root := none
  }
  have pogDefs'_empty : st.pogDefs' = ∅ := by
    simp [CheckerStateData.pogDefs', HashSet.not_contains_empty]
  have pogDefsTerm_tr : st.pogDefsTerm = ⊤ := by
    rw [CheckerStateData.pogDefsTerm, pogDefs'_empty]
    apply ClauseDb.toPropTermSub_emptySet
  let pfs := {
    equivalent_clauseDb := by
      rw [ClauseDb.toPropTerm_ofICnf]
      apply PropTerm.equivalentOver_refl
    contains_pogDefs := by
      simp [pogDefs'_empty]
    uep_pogDefs := by
      simp only [pogDefsTerm_tr, PropTerm.semVars_tr, Finset.coe_empty]
      exact PropTerm.hasUniqueExtension_to_empty _ _
    -- LATER: Prove these when we are sure they imply the result.
    clauseDb_depVars := sorry
    depVars_pog := sorry
    vars_orig := sorry
    decomposable_lits := by
      simp [hInitPog, decomposable_lit]
    equivalent_lits := by
      simp [pogDefsTerm_tr, hInitPog, PropTerm.equivalentOver_refl]
  }
  return ⟨st, pfs⟩

/-- Check if `C` is an asymmetric tautology wrt the clause database. `C` must not already be
a tautology. -/
def checkAtWithHints' (db : ClauseDb ClauseIdx) (C : IClause) (hC : C.toPropTerm ≠ ⊤)
    (hints : Array ClauseIdx) :
    Except CheckerError { _u : Unit // db.toPropTermSub (· ∈ hints.data) ≤ C.toPropTerm }
:= do
  match db.unitPropWithHintsDep C.toFalsifyingAssignment hints with
  | .contradiction h => return ⟨(), (by
      rw [IClause.toPropTerm_toFalsifyingAssignment C hC, ← le_himp_iff, himp_bot, compl_compl] at h
      assumption)⟩
  | .extended τ _ => throw <| .upNoContradiction τ
  | .hintNotUnit idx C σ => throw <| .hintNotUnit idx C σ
  | .hintNonexistent idx => throw <| .unknownClauseIdx idx

/-- Check if `C` is an asymmetric tautology wrt the clause database, or simply a tautology. -/
def checkAtWithHints (db : ClauseDb ClauseIdx) (C : IClause) (hints : Array ClauseIdx) :
    Except CheckerError { _u : Unit // db.toPropTermSub (· ∈ hints.data) ≤ C.toPropTerm }
:= do
  -- TODO: We could maintain no-tautologies-in-clause-db as an invariant rather than dynamically
  -- checking. Checking on every deletion could cause serious slowdown (but measure first!).
  if hTauto : C.toPropTerm = ⊤ then
    return ⟨(), by simp [hTauto]⟩
  else
    checkAtWithHints' db C hTauto hints

def addClause (db₀ : ClauseDb ClauseIdx) (idx : ClauseIdx) (C : IClause) :
    Except CheckerError { db : ClauseDb ClauseIdx // db = db₀.addClause idx C ∧ ¬db₀.contains idx }
:= do
  if h : db₀.contains idx then
    throw <| .duplicateClauseIdx idx
  else
    return ⟨db₀.addClause idx C, rfl, h⟩

def addAt (idx : ClauseIdx) (C : IClause) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨_, hImp⟩ ← checkAtWithHints st.clauseDb C hints
  let ⟨db', hAdd, hContains⟩ ← addClause st.clauseDb idx C
  let st' := { st with
    clauseDb := db'
  }
  have hDb : st'.clauseDb.toPropTerm = st.clauseDb.toPropTerm := by
    simp [hAdd, st.clauseDb.toPropTerm_addClause' _ _ hContains,
      st.clauseDb.toPropTerm_subset _ |>.trans hImp]
  have hPogDefs' : db'.toPropTermSub st.pogDefs' = st.pogDefsTerm := by
    have : ¬idx ∈ st.pogDefs' := fun h =>
      hContains (pfs.contains_pogDefs _ h)
    rw [CheckerStateData.pogDefsTerm, hAdd, st.clauseDb.toPropTermSub_addClause_of_not_mem C this]
  have hPogDefs : st'.pogDefsTerm = st.pogDefsTerm := by
    rw [CheckerStateData.pogDefsTerm]
    exact hPogDefs'
  let pfs' := { pfs with
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    contains_pogDefs := fun idx h => by
      have := pfs.contains_pogDefs idx h
      simp only [hAdd]
      exact st.clauseDb.contains_addClause _ _ _ |>.mpr (Or.inl this)
    uep_pogDefs := hPogDefs ▸ pfs.uep_pogDefs
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
    clauseDb_depVars := hDb ▸ pfs.clauseDb_depVars
  }
  set (σ := CheckerState) ⟨st', pfs'⟩

def delAt (idx : ClauseIdx) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let some C := st.clauseDb.getClause idx
    | throw <| .unknownClauseIdx idx
  -- TODO: need additional check that `idx` is not a scheme def
  let db' := st.clauseDb.delClause idx
  -- The clause is AT by everything except itself.
  let hImp ← checkAtWithHints db' C hints
  let st' := { st with
    clauseDb := db'
  }
  have hDb : st'.clauseDb.toPropTerm = st.clauseDb.toPropTerm := by
    sorry
  have hPogDefs' : db'.toPropTermSub st.pogDefs' = st.pogDefsTerm := by
    sorry
  have hPogDefs : st'.pogDefsTerm = st.pogDefsTerm := by
    sorry
  let pfs' := { pfs with
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    contains_pogDefs := fun idx h =>
      sorry
    uep_pogDefs := hPogDefs ▸ pfs.uep_pogDefs
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
    clauseDb_depVars := hDb ▸ pfs.clauseDb_depVars
  }
  set (σ := CheckerState) ⟨st', pfs'⟩

def addProd (idx : ClauseIdx) (x : Var) (ls : Array ILit) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

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
  let ⟨db₁, _⟩ ← addClause st.clauseDb idx (ls.map (-·) |>.push (.mkPos x))
  let mut (db, pogDefs) := (db₁, st.pogDefs.insert idx)
  for h : i in [0:ls.size] do
    let l := ls[i]'(Membership.mem.upper h)
    let ⟨dbᵢ, _⟩ ← addClause db (idx+i+1) #[.mkNeg x, l]
    db := dbᵢ
    pogDefs := pogDefs.insert (idx+i+1)

  let pog' ← match st.pog.addConj x ls with
    | .ok s => pure s
    | .error e => throw <| .graphUpdateError e

  let st' := { st with
    clauseDb := db
    depVars := st.depVars.insert x union
    pog := pog'
    pogDefs := pogDefs
  }
  let pfs' := {
    equivalent_clauseDb := sorry
    equivalent_lits := sorry
    contains_pogDefs := sorry
    uep_pogDefs := sorry
    clauseDb_depVars := sorry
    decomposable_lits := sorry
    vars_orig := sorry
    depVars_pog := sorry
  }
  set (σ := CheckerState) ⟨st', pfs'⟩

def addSum (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (hints : Array ClauseIdx) :
    CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

  -- Check that added variable is fresh.
  if st.depVars.contains x then
    throw <| .duplicateExtVar x

  -- Check that variables are known and compute their dependencies.
  let some D₁ := st.depVars.find? l₁.var
    | throw <| .unknownVar l₁.var
  let some D₂ := st.depVars.find? l₂.var
    | throw <| .unknownVar l₂.var

  -- Check that variables are mutually exclusive.
  -- TODO: Check that hints are only using POG defs.
  let _ ← checkAtWithHints st.clauseDb #[-l₁, -l₂] hints

  let ⟨db₁, _⟩ ← addClause st.clauseDb idx #[.mkNeg x, l₁, l₂]
  let ⟨db₂, _⟩ ← addClause db₁ (idx+1) #[.mkPos x, -l₁]
  let ⟨db₃, _⟩ ← addClause db₂ (idx+2) #[.mkPos x, -l₂]

  let pog' ← match st.pog.addDisj x l₁ l₂ with
    | .ok s => pure s
    | .error e => throw <| .graphUpdateError e

  let st' := { st with
    clauseDb := db₃
    pogDefs := st.pogDefs.insert idx |>.insert (idx + 1) |>.insert (idx + 2)
    depVars := st.depVars.insert x (D₁.union D₂)
    pog := pog'
  }
  let pfs' := {
    equivalent_clauseDb := sorry
    equivalent_lits := sorry
    contains_pogDefs := sorry
    uep_pogDefs := sorry
    clauseDb_depVars := sorry
    decomposable_lits := sorry
    vars_orig := sorry
    depVars_pog := sorry
  }
  set (σ := CheckerState) ⟨st', pfs'⟩

def setRoot (r : ILit) : CheckerM Unit := do
  modify fun ⟨st, pfs⟩ => ⟨{ st with root := some r }, { pfs with }⟩

-- TODO: final invariant `st.root = some r ∧ st.inputCnf.toPropTerm = ⟦st.scheme.toPropForm r⟧`
def checkFinalState : CheckerM Unit := do
  let ⟨st, _⟩ ← get

  let some r := st.root
    | throw <| .finalRootNotSet

  -- NOTE: Looping over the entire clause db is not necessary. We could store the number `nClauses`
  -- and as long as `nClauses = st.pogDefs.size + 1` (`+ 1` for the root literal) at the end,
  -- the conclusion follows.
  let _ ← st.clauseDb.foldM (init := ()) fun _ idx C => do
    if C != #[r] && !st.pogDefs.contains idx then
      throw <| .finalClauseInvalid idx C

def checkProofStep (step : CratStep) : CheckerM Unit :=
  match step with
  | .addAt idx C hints => addAt idx C hints
  | .delAt idx hints => delAt idx hints
  | .prod idx x ls => addProd idx x ls
  | .sum idx x l₁ l₂ hints => addSum idx x l₁ l₂ hints
  | .root r => setRoot r

-- def count (r : Var) : CheckerCoreM Nat := do
--   let st ← get
--   st.scheme.count r st.origVars.size

def checkProof (cnf : ICnf) (pf : Array CratStep) : Except CheckerError Unit := do
  let mut st : CheckerState ← initial cnf
  let x : CheckerM Unit := do
    for step in pf do
      checkProofStep step
    checkFinalState
  let (ret, _) := x.run st |>.run
  ret

#exit

-- LATER: re-add tracing

/-- Wraps a well-formed checker state with extra stuff for tracing and debugging it. -/
structure CheckerState' where
  core : CheckerState
  verbose : Bool := false
  trace : Array String := #[]

namespace CheckerState

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