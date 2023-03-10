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
  | pogDefClause (idx : ClauseIdx)
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
    | pogDefClause idx => s!"clause at index {idx} cannot be deleted because it is a POG definition"
    | hintNotUnit idx C σ =>
      s!"hinted clause {C} at index {idx} did not become unit under assignment {σ}"
    | upNoContradiction τ =>
      s!"unit propagation did not derive contradiction (final assignment {τ})"
    | duplicateExtVar x => s!"extension variable {x} was already introduced"
    | unknownVar x => s!"unknown variable {x}"
    | depsNotDisjoint xs => s!"variables {xs} have non-disjoint dependency sets"
    | finalRootNotSet => s!"proof done but root literal was not asserted"
    | finalClauseInvalid idx C =>
      s!"proof done but clause {C} at index {idx} is neither the asserted root nor a POG definition"

end CheckerError

structure ClausalData where
  /-- The clause database. -/
  clauseDb : ClauseDb ClauseIdx
  /-- Which clauses are POG definition clauses. -/
  pogDefs : HashSet ClauseIdx

def ClausalData.pogDefs' (st : ClausalData) : Set ClauseIdx :=
  { idx | st.pogDefs.contains idx }

noncomputable def ClausalData.pogDefsTerm (st : ClausalData) : PropTerm Var :=
  st.clauseDb.toPropTermSub st.pogDefs'

/-- The clausal state `st` is well-formed with respect to an original formula `φ₀`. -/
structure ClausalData.WF (st : ClausalData) (φ₀ : PropTerm Var) : Prop where
  /-- The POG definition clauses are all in the clause database. -/
  pogDefs_in_clauseDb : ∀ idx : ClauseIdx, idx ∈ st.pogDefs' → st.clauseDb.contains idx

  /-- The clause database is equivalent to the original formula over original variables. -/
  equivalent_clauseDb : PropTerm.equivalentOver φ₀.semVars φ₀ st.clauseDb.toPropTerm

  /-- The POG definition clauses extend uniquely from the original variables to their current set
  of variables. -/
  uep_pogDefsTerm : PropTerm.hasUniqueExtension X₀ st.pogDefsTerm.semVars st.pogDefsTerm
  
def ClausalState (φ₀ : PropTerm Var) := { st : ClausalData // st.WF φ₀ }

structure GraphData where
  /-- The partitioned-operation graph. -/
  pog : Pog

  /-- Maps any variable present in `pog` to the set of all *original* variables it depends on.
  For example, an original `x` is mapped to `{x}` whereas an extension `p` with `p ↔ x ∧ y` is
  mapped to `{x, y}`.

  Variables not present in `pog` are not present in this map. Thus we maintain the invariant
  that a variable is in the `pog` iff it is in the domain of this map. -/
  depVars : HashMap Var (HashSet Var)

  /-- The POG root literal, if we already saw a `root` instruction. Otherwise `none`. -/
  root : Option ILit

/-- The graph state `st` is well-formed with respect to the set `X₀` of original variables . -/
structure GraphData.WF (st : GraphData) (X₀ : Finset Var) : Prop where
  /-- Variable dependencies are correctly stored in `depVars`. -/
  depVars_pog : ∀ (l : ILit) (D : HashSet Var), st.depVars.find? l.var = some D →
    (st.pog.toPropForm l).vars = D.toFinset

  /-- Every formula in the POG forest lives over the original variables. -/
  pog_vars : ∀ l : ILit, st.depVars.contains l.var → (st.pog.toPropForm l).vars ⊆ X₀

  /-- Every formula in the POG forest is decomposable. For literals not defining anything in the
  forest this still holds by fiat because `st.pog.toPropForm l = l.toPropForm`. -/
  decomposable : ∀ l : ILit, (st.pog.toPropForm l).decomposable
  
def GraphState (X₀ : Finset Var) := { st : GraphData // st.WF X₀ }

/-- The checker's runtime state. Contains exactly the data needed to fully check a proof. -/
structure Data where
  inputCnf : ICnf
  /-- The variables present in the original CNF. -/
  -- TODO: not used at the moment; its cardinality is needed to output an absolute model-count,
  -- and also to state invariants; but for the latter, ghost state would suffice
  origVars : HashSet Var
  clauses : ClausalData
  graph : GraphData

structure Data.WF (st : Data) : Prop where
  clausesWF : st.clauses.WF st.inputCnf.toPropTerm
  graphWF : st.graph.WF st.inputCnf.vars.toFinset

  /-- `depVars` contains all variables that influence the clause database. Contrapositive:
  if a variable is not in `depVars` then it does not influence the clause database so can be
  defined as an extension variable. -/
  clauseDb_depVars : ∀ x : Var,
    x ∈ st.clauses.clauseDb.toPropTerm.semVars → st.graph.depVars.contains x

  /-- In the context of the POG defining clauses, every variable is s-equivalent over original
  variables to what it defines in the POG forest. -/
  -- TODO: need `st.depVars.contains x` as precondition?
  equivalent_lits : ∀ l : ILit, PropTerm.equivalentOver st.inputCnf.toPropTerm.semVars
    (l.toPropTerm ⊓ st.clauses.pogDefsTerm)
    ⟦st.graph.pog.toPropForm l⟧

def State := { st : Data // st.WF}

abbrev CheckerM := ExceptT CheckerError <| StateM State

def initialClauses (inputCnf : ICnf) :
    { c : ClausalData // c.WF inputCnf.toPropTerm ∧ c.pogDefsTerm = ⊤ } :=
  let st := {
    clauseDb := .ofICnf inputCnf
    pogDefs := .empty ClauseIdx
  }
  have pogDefs'_empty : st.pogDefs' = ∅ := by
    simp [ClausalData.pogDefs', HashSet.not_contains_empty]
  have pogDefsTerm_tr : st.pogDefsTerm = ⊤ := by
    rw [ClausalData.pogDefsTerm, pogDefs'_empty]
    apply ClauseDb.toPropTermSub_emptySet
  let pfs := {
    pogDefs_in_clauseDb := by
      simp [pogDefs'_empty]
    equivalent_clauseDb := by
      rw [ClauseDb.toPropTerm_ofICnf]
      apply PropTerm.equivalentOver_refl
    uep_pogDefsTerm := by
      simp only [pogDefsTerm_tr, PropTerm.semVars_tr, Finset.coe_empty]
      exact PropTerm.hasUniqueExtension_to_empty _ _
  }
  ⟨st, pfs, pogDefsTerm_tr⟩

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
    
def initialGraph (inputCnf : ICnf) :
    Except CheckerError { g : GraphData // g.WF inputCnf.vars.toFinset ∧
      ∀ l, g.pog.toPropForm l = l.toPropForm } := do
  let ⟨initPog, hInitPog⟩ ← initialPog inputCnf
  let st := {
    pog := initPog
    depVars := inputCnf.vars.fold (init := .empty) fun s x =>
      s.insert x (HashSet.empty Var |>.insert x)
    root := none
  }
  let pfs := {
    -- LATER: Prove these when we are sure they imply the result.
    depVars_pog := sorry
    pog_vars := sorry
    decomposable := by
      simp [hInitPog, decomposable_lit]
  }
  return ⟨st, pfs, by simp [hInitPog]⟩

def initial (inputCnf : ICnf) : Except CheckerError State := do
  let ⟨initC, initCWF, initCTr⟩ := initialClauses inputCnf 
  let ⟨initG, initGWF, initGId⟩ ← initialGraph inputCnf
  let st := {
    inputCnf
    origVars := inputCnf.vars
    clauses := initC
    graph := initG
  }
  let pfs := {
    clausesWF := initCWF
    graphWF := initGWF
    -- LATER: Prove these when we are sure they imply the result.
    clauseDb_depVars := sorry
    equivalent_lits := by
      simp [initCTr, initGId, PropTerm.equivalentOver_refl]
  }
  return ⟨st, pfs⟩

/-- Check if `C` is an asymmetric tautology wrt the clause database. `C` must not be a tautology. -/
def checkAtWithHints (db : ClauseDb ClauseIdx) (C : IClause) (hC : C.toPropTerm ≠ ⊤)
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
def checkImpliedWithHints (db : ClauseDb ClauseIdx) (C : IClause) (hints : Array ClauseIdx) :
    Except CheckerError { _u : Unit // db.toPropTermSub (· ∈ hints.data) ≤ C.toPropTerm }
:= do
  -- TODO: We could maintain no-tautologies-in-clause-db as an invariant rather than dynamically
  -- checking. Checking on every deletion could cause serious slowdown (but measure first!).
  if hTauto : C.toPropTerm = ⊤ then
    return ⟨(), by simp [hTauto]⟩
  else
    checkAtWithHints db C hTauto hints

def addClause (db₀ : ClauseDb ClauseIdx) (idx : ClauseIdx) (C : IClause) :
    Except CheckerError { db : ClauseDb ClauseIdx // db = db₀.addClause idx C ∧ ¬db₀.contains idx }
:= do
  if h : db₀.contains idx then
    throw <| .duplicateClauseIdx idx
  else
    return ⟨db₀.addClause idx C, rfl, h⟩

def addAtAux (φ₀ : PropTerm Var) (c₀ : ClausalState φ₀) (idx : ClauseIdx) (C : IClause)
    (hints : Array ClauseIdx) : Except CheckerError
      { c : ClausalData // c.WF φ₀ ∧ c.clauseDb.toPropTerm = c₀.val.clauseDb.toPropTerm
        ∧ c.pogDefsTerm = c₀.val.pogDefsTerm } := do
  let ⟨dat, pfs⟩ := c₀
  let ⟨_, hImp⟩ ← checkImpliedWithHints dat.clauseDb C hints
  let ⟨db', hAdd, hContains⟩ ← addClause dat.clauseDb idx C
  let dat' := { dat with clauseDb := db' }
  have hDb : dat'.clauseDb.toPropTerm = dat.clauseDb.toPropTerm := by
    simp only [hAdd, dat.clauseDb.toPropTerm_addClause_eq _ _ hContains]
    simp [dat.clauseDb.toPropTerm_subset _ |>.trans hImp]
  have hPogDefs' : db'.toPropTermSub dat.pogDefs' = dat.pogDefsTerm := by
    have : ¬idx ∈ dat.pogDefs' := fun h =>
      hContains (pfs.pogDefs_in_clauseDb _ h)
    rw [ClausalData.pogDefsTerm, hAdd, dat.clauseDb.toPropTermSub_addClause_of_not_mem C this]
  have hPogDefs : dat'.pogDefsTerm = dat.pogDefsTerm := hPogDefs'
  have pfs' := {
    pogDefs_in_clauseDb := fun idx h => by
      have := pfs.pogDefs_in_clauseDb idx h
      simp only [hAdd]
      exact dat.clauseDb.contains_addClause _ _ _ |>.mpr (Or.inl this)
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    uep_pogDefsTerm := hPogDefs ▸ pfs.uep_pogDefsTerm
  }
  return ⟨dat', pfs', hDb, hPogDefs⟩

def addAt (idx : ClauseIdx) (C : IClause) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨c', cWF, hDb, hPogDefs⟩ ←
    addAtAux st.inputCnf.toPropTerm ⟨st.clauses, pfs.clausesWF⟩ idx C hints
  let st' := { st with clauses := c' }
  have pfs' := { pfs with
    clausesWF := cWF
    clauseDb_depVars := hDb ▸ pfs.clauseDb_depVars
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
  }
  set (σ := State) ⟨st', pfs'⟩

def getClause (db : ClauseDb ClauseIdx) (idx : ClauseIdx) :
    Except CheckerError { C : IClause // db.getClause idx = some C } :=
  match db.getClause idx with
  | some C => return ⟨C, rfl⟩
  | none => throw <| .unknownClauseIdx idx

def delAtAux (φ₀ : PropTerm Var) (c₀ : ClausalState φ₀) (idx : ClauseIdx) (hints : Array ClauseIdx)
    : Except CheckerError
      { c : ClausalData // c.WF φ₀ ∧ c.clauseDb.toPropTerm = c₀.val.clauseDb.toPropTerm
        ∧ c.pogDefsTerm = c₀.val.pogDefsTerm } := do
  let ⟨dat, pfs⟩ := c₀
  let ⟨C, hGet⟩ ← getClause dat.clauseDb idx
  -- NOTE: We could investigate whether the check is really necessary.
  let ⟨_, hMem⟩ ← (if h : dat.pogDefs.contains idx then
      throw <| .pogDefClause idx
    else
      pure ⟨(), h⟩
    : Except CheckerError { _u : Unit // idx ∉ dat.pogDefs' })
  let db' := dat.clauseDb.delClause idx
  -- The clause is AT by everything except itself.
  let ⟨_, hImp⟩ ← checkImpliedWithHints db' C hints
  let dat' := { dat with clauseDb := db' }
  have hDb : dat'.clauseDb.toPropTerm = dat.clauseDb.toPropTerm := by
    have : dat'.clauseDb.toPropTerm = dat'.clauseDb.toPropTerm ⊓ C.toPropTerm := by
      have := dat'.clauseDb.toPropTerm_subset _ |>.trans hImp
      exact left_eq_inf.mpr this
    rw [this]
    simp [dat.clauseDb.toPropTerm_delClause_eq _ _ hGet]
  have hPogDefs' : db'.toPropTermSub dat.pogDefs' = dat.pogDefsTerm :=
    dat.clauseDb.toPropTermSub_delClause_of_not_mem hMem
  have hPogDefs : dat'.pogDefsTerm = dat.pogDefsTerm := hPogDefs'
  have pfs' := {
    pogDefs_in_clauseDb := fun idx h => by
      refine dat.clauseDb.contains_delClause _ _ |>.mpr ⟨pfs.pogDefs_in_clauseDb idx h, ?_⟩
      intro hEq
      exact hMem (hEq.symm ▸ h)
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    uep_pogDefsTerm := hPogDefs ▸ pfs.uep_pogDefsTerm
  }
  return ⟨dat', pfs', hDb, hPogDefs⟩

def delAt (idx : ClauseIdx) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨c', cWF, hDb, hPogDefs⟩ ←
    delAtAux st.inputCnf.toPropTerm ⟨st.clauses, pfs.clausesWF⟩ idx hints
  let st' := { st with clauses := c' }
  have pfs' := { pfs with
    clausesWF := cWF
    clauseDb_depVars := hDb ▸ pfs.clauseDb_depVars
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
  }
  set (σ := State) ⟨st', pfs'⟩

def addProd (idx : ClauseIdx) (x : Var) (ls : Array ILit) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

  -- Check that added variable is fresh.
  if st.graph.depVars.contains x then
    throw <| .duplicateExtVar x

  -- Check that variables are known and compute their dependencies.
  let Ds ← ls.mapM fun l =>
    match st.graph.depVars.find? l.var with
    | some D => pure D
    | none => throw <| .unknownVar l.var

  -- Compute total dependency set and check pairwise disjointness.
  let (union, disjoint) := HashSet.Union' Ds
  if !disjoint then
    throw <| .depsNotDisjoint (ls.toList.map ILit.var)

  -- Defining clauses for the conjunction.
  let ⟨db₁, _⟩ ← addClause st.clauses.clauseDb idx (ls.map (-·) |>.push (.mkPos x))
  let mut (db, pogDefs) := (db₁, st.clauses.pogDefs.insert idx)
  for h : i in [0:ls.size] do
    let l := ls[i]'(Membership.mem.upper h)
    let ⟨dbᵢ, _⟩ ← addClause db (idx+i+1) #[.mkNeg x, l]
    db := dbᵢ
    pogDefs := pogDefs.insert (idx+i+1)

  let pog' ← match st.graph.pog.addConj x ls with
    | .ok s => pure s
    | .error e => throw <| .graphUpdateError e

  let st' := { st with
    clauses := {
      clauseDb := db
      pogDefs
    }
    graph := {
      pog := pog'
      depVars := st.graph.depVars.insert x union
      root := st.graph.root
    }
  }
  have pfs' := sorry
  set (σ := State) ⟨st', pfs'⟩

def addSum (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (hints : Array ClauseIdx) :
    CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

  -- Check that added variable is fresh.
  if st.graph.depVars.contains x then
    throw <| .duplicateExtVar x

  -- Check that variables are known and compute their dependencies.
  let some D₁ := st.graph.depVars.find? l₁.var
    | throw <| .unknownVar l₁.var
  let some D₂ := st.graph.depVars.find? l₂.var
    | throw <| .unknownVar l₂.var

  let pog' ← match st.graph.pog.addDisj x l₁ l₂ with
    | .ok s => pure s
    | .error e => throw <| .graphUpdateError e


  -- This check combines clausal and POG reasoning
  -- Check that variables are mutually exclusive.
  -- TODO: Check that hints are only using POG defs.
  -- NOTE: Important that this be done before adding clauses, for linearity.
  let _ ← checkImpliedWithHints st.clauses.clauseDb #[-l₁, -l₂] hints

  let ⟨db₁, _⟩ ← addClause st.clauses.clauseDb idx #[.mkNeg x, l₁, l₂]
  let ⟨db₂, _⟩ ← addClause db₁ (idx+1) #[.mkPos x, -l₁]
  let ⟨db₃, _⟩ ← addClause db₂ (idx+2) #[.mkPos x, -l₂]

  -- have : db₃.toPropTerm = st.clauseDb.toPropTerm ⊓ (.biImpl (.var x) (l₁.toPropTerm ⊔ l₂.toPropTerm)) :=
  --   sorry

  let st' := { st with
    clauses := {
      clauseDb := db₃
      pogDefs := st.clauses.pogDefs.insert idx |>.insert (idx + 1) |>.insert (idx + 2)
    }
    graph := {
      pog := pog'
      depVars := st.graph.depVars.insert x (D₁.union D₂)
      root := st.graph.root
    }
  }
  have pfs' := sorry
  set (σ := State) ⟨st', pfs'⟩

def setRoot (r : ILit) : CheckerM Unit := do
  modify fun ⟨st, pfs⟩ =>
    ⟨{ st with graph := { st.graph with root := some r } },
     { pfs with graphWF := { pfs.graphWF with } }⟩

-- TODO: final invariant `st.root = some r ∧ st.inputCnf.toPropTerm = ⟦st.scheme.toPropForm r⟧`
def checkFinalState : CheckerM Unit := do
  let ⟨st, _⟩ ← get

  let some r := st.graph.root
    | throw <| .finalRootNotSet

  -- NOTE: Looping over the entire clause db is not necessary. We could store the number `nClauses`
  -- and as long as `nClauses = st.pogDefs.size + 1` (`+ 1` for the root literal) at the end,
  -- the conclusion follows.
  let _ ← st.clauses.clauseDb.foldM (init := ()) fun _ idx C => do
    if C != #[r] && !st.clauses.pogDefs.contains idx then
      throw <| .finalClauseInvalid idx C

def checkProofStep (step : CratStep) : CheckerM Unit :=
  match step with
  | .addAt idx C hints => addAt idx C hints
  | .delAt idx hints => delAt idx hints
  | .prod idx x ls => addProd idx x ls
  | .sum idx x l₁ l₂ hints => addSum idx x l₁ l₂ hints
  | .root r => setRoot r

-- def count (r : Var) : CheckerM Nat := do
--   let ⟨st, _⟩ ← get
--   st.graph.pog.count r st.origVars.size

def checkProof (cnf : ICnf) (pf : Array CratStep) : Except CheckerError Unit := do
  let mut st : State ← initial cnf
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