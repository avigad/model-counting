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

/-- The checker's runtime state. Contains exactly the data needed to fully check a proof.
It can be ill-formed, so it's a "pre"-well-formed state. -/
structure PreState where
  inputCnf : ICnf

  /-- The variables present in the original CNF. -/
  -- TODO: not used at the moment; its cardinality is needed to output an absolute model-count,
  -- and also to state invariants; but for the latter, ghost state would suffice
  origVars : HashSet Var

  /-- The clause database. -/
  clauseDb : ClauseDb ClauseIdx

  /-- Which clauses are POG definition clauses. -/
  pogDefs : HashSet ClauseIdx

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

def PreState.pogDefs' (st : PreState) : Finset ClauseIdx :=
  st.pogDefs.toFinset

noncomputable def PreState.pogDefsTerm (st : PreState) : PropTerm Var :=
  st.clauseDb.toPropTermSub st.pogDefs'

def PreState.allVars (st : PreState) : Set Var :=
  { x | st.depVars.contains x }

structure PreState.WF (st : PreState) : Prop where
  /-- The POG definition clauses are all in the clause database. -/
  pogDefs_in_clauseDb : ∀ idx : ClauseIdx, idx ∈ st.pogDefs' → st.clauseDb.contains idx

  /-- Variable dependencies are correctly stored in `depVars`. -/
  depVars_pog : ∀ (l : ILit) (D : HashSet Var), st.depVars.find? l.var = some D →
    -- NOTE: can strengthen to eq if needed
    (st.pog.toPropForm l).vars ⊆ D.toFinset

  /-- Every formula in the POG forest is partitioned.

  For literals not defining anything in the forest this still holds by fiat because
  `st.pog.toPropForm l = l.toPropForm`. -/
  partitioned : ∀ x : Var, (st.pog.toPropForm (.mkPos x)).partitioned

  /-- `depVars` contains all variables that influence the clause database. Contrapositive:
  if a variable is not in `depVars` then it does not influence the clause database so can be
  defined as an extension variable. -/
  clauseDb_semVars_sub : ↑st.clauseDb.toPropTerm.semVars ⊆ st.allVars

  pogDefsTerm_semVars_sub : ↑st.pogDefsTerm.semVars ⊆ st.allVars

  inputCnf_semVars_sub : ↑st.inputCnf.toPropTerm.semVars ⊆ st.allVars

  /-- The clause database is equivalent to the original formula over original variables. -/
  equivalent_clauseDb : PropTerm.equivalentOver st.inputCnf.vars.toFinset
    st.inputCnf.toPropTerm st.clauseDb.toPropTerm

  /-- Every formula in the POG forest lives over the original variables. -/
  pog_vars : ∀ x : Var, x ∈ st.allVars →
    (st.pog.toPropForm (.mkPos x)).vars ⊆ st.inputCnf.vars.toFinset

  /-- The POG definition clauses extend uniquely from the original variables to the current set
  of variables. -/
  uep_pogDefsTerm : PropTerm.hasUniqueExtension st.inputCnf.vars.toFinset st.allVars
    st.pogDefsTerm

  /-- In the context of the POG defining clauses, every variable is s-equivalent over original
  variables to what it defines in the POG forest. -/
  -- TODO: need `x ∈ st.graph.allVars` as precondition?
  -- NOTE: It appears this really must quantify over literals and not just variables like some
  -- of the other invariants.
  equivalent_lits : ∀ l : ILit, PropTerm.equivalentOver st.inputCnf.vars.toFinset
    (l.toPropTerm ⊓ st.pogDefsTerm)
    ⟦st.pog.toPropForm l⟧
  
theorem PreState.WF.partitioned' {st : PreState} (hWf : st.WF) (l : ILit) :
    (st.pog.toPropForm l).partitioned :=
  l.mkPos_or_mkNeg.elim (· ▸ hWf.partitioned l.var) fun h => by
    rw [h, Pog.toPropForm_neg]
    exact hWf.partitioned l.var
    
theorem PreState.WF.pog_vars' {st : PreState} (hWf : st.WF) (l : ILit) :
    l.var ∈ st.allVars → (st.pog.toPropForm l).vars ⊆ st.inputCnf.vars.toFinset :=
  fun hMem => l.mkPos_or_mkNeg.elim (· ▸ hWf.pog_vars l.var hMem) fun h => by
    rw [h, Pog.toPropForm_neg]
    exact hWf.pog_vars l.var hMem

/-- A well-formed checker state. -/
def State := { st : PreState // st.WF }

abbrev CheckerM := ExceptT CheckerError <| StateM State

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

def initial (inputCnf : ICnf) : Except CheckerError State := do
  let ⟨initPog, hInitPog⟩ ← initialPog inputCnf
  let st := {
    inputCnf
    origVars := inputCnf.vars
    clauseDb := .ofICnf inputCnf
    pogDefs := .empty ClauseIdx
    pog := initPog
    depVars := inputCnf.vars.fold (init := .empty) fun s x =>
      s.insert x (HashSet.empty Var |>.insert x)
    root := none
  }
  have pogDefs'_empty : st.pogDefs' = ∅ := by
    simp [PreState.pogDefs', HashSet.not_contains_empty]
  have pogDefsTerm_tr : st.pogDefsTerm = ⊤ := by
    rw [PreState.pogDefsTerm, pogDefs'_empty, Finset.coe_empty]
    apply ClauseDb.toPropTermSub_emptySet
  have allVars_eq : st.allVars = st.inputCnf.vars.toFinset := by
    -- LATER: Prove these when we are sure they imply the result.
    sorry
  have pfs := {
    pogDefs_in_clauseDb := by
      simp [pogDefs'_empty]
    -- LATER: Prove these when we are sure they imply the result.
    depVars_pog := sorry
    partitioned := by
      simp [hInitPog, PropForm.partitioned]
    clauseDb_semVars_sub := by
      rw [allVars_eq, ClauseDb.toPropTerm_ofICnf]
      apply ICnf.semVars_sub
    pogDefsTerm_semVars_sub := by
      rw [pogDefsTerm_tr, PropTerm.semVars_tr, Finset.coe_empty]
      apply Set.empty_subset
    inputCnf_semVars_sub := by
      rw [allVars_eq]
      apply ICnf.semVars_sub
    equivalent_clauseDb := by
      rw [ClauseDb.toPropTerm_ofICnf]
      apply PropTerm.equivalentOver_refl
    pog_vars := by
      simp [allVars_eq, hInitPog, PropForm.vars]
    uep_pogDefsTerm := by
      simp only [pogDefsTerm_tr, PropTerm.semVars_tr, Finset.coe_empty, allVars_eq]
      exact PropTerm.hasUniqueExtension_refl _ _
    equivalent_lits := by
      simp [pogDefsTerm_tr, hInitPog, PropTerm.equivalentOver_refl]
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
    Except CheckerError { db : ClauseDb ClauseIdx //
      db = db₀.addClause idx C ∧
      ¬db₀.contains idx ∧
      -- This is just for convenience as it can be proven directly from the other postconditions.
      db.toPropTerm = db₀.toPropTerm ⊓ C.toPropTerm } := do
  if h : db₀.contains idx then
    throw <| .duplicateClauseIdx idx
  else
    return ⟨db₀.addClause idx C, rfl, h, db₀.toPropTerm_addClause_eq idx C h⟩

def addAt (idx : ClauseIdx) (C : IClause) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨_, hImp⟩ ← checkImpliedWithHints st.clauseDb C hints
  let ⟨db', hAdd, hContains, hEq⟩ ← addClause st.clauseDb idx C
  let st' := { st with clauseDb := db' }
  have hDb : st'.clauseDb.toPropTerm = st.clauseDb.toPropTerm := by
    simp [hEq, st.clauseDb.toPropTerm_subset _ |>.trans hImp]
  have hPogDefs : st'.pogDefsTerm = st.pogDefsTerm := by
    have hMem : idx ∉ (st.pogDefs' : Set _) := fun h =>
      hContains (pfs.pogDefs_in_clauseDb _ h)
    have : st'.pogDefs' = st.pogDefs' := rfl
    rw [PreState.pogDefsTerm, this]
    simp [PreState.pogDefsTerm, hAdd, st.clauseDb.toPropTermSub_addClause_of_not_mem C hMem]
  have pfs' := { pfs with
    pogDefs_in_clauseDb := fun idx h => by
      have := pfs.pogDefs_in_clauseDb idx h
      simp only [hAdd]
      exact st.clauseDb.contains_addClause _ _ _ |>.mpr (Or.inl this)
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    clauseDb_semVars_sub := hDb ▸ pfs.clauseDb_semVars_sub
    pogDefsTerm_semVars_sub := hPogDefs ▸ pfs.pogDefsTerm_semVars_sub
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
    uep_pogDefsTerm := hPogDefs ▸ pfs.uep_pogDefsTerm
  }
  set (σ := State) ⟨st', pfs'⟩

def getClause (db : ClauseDb ClauseIdx) (idx : ClauseIdx) :
    Except CheckerError { C : IClause // db.getClause idx = some C } :=
  match db.getClause idx with
  | some C => return ⟨C, rfl⟩
  | none => throw <| .unknownClauseIdx idx

def delAt (idx : ClauseIdx) (hints : Array ClauseIdx) : CheckerM Unit := do
  let ⟨st, pfs⟩ ← get
  let ⟨C, hGet⟩ ← getClause st.clauseDb idx
  -- NOTE: We could investigate whether the check is really necessary.
  let ⟨_, hMem⟩ ← (if h : st.pogDefs.contains idx then
      throw <| .pogDefClause idx
    else
      pure ⟨(), HashSet.not_mem_toFinset _ _ |>.mpr h⟩
    : Except CheckerError { _u : Unit // idx ∉ st.pogDefs' })
  let db' := st.clauseDb.delClause idx
  -- The clause is AT by everything except itself.
  let ⟨_, hImp⟩ ← checkImpliedWithHints db' C hints
  let st' := { st with clauseDb := db' }
  have hDb : st'.clauseDb.toPropTerm = st.clauseDb.toPropTerm := by
    have : st'.clauseDb.toPropTerm = st'.clauseDb.toPropTerm ⊓ C.toPropTerm := by
      have := st'.clauseDb.toPropTerm_subset _ |>.trans hImp
      exact left_eq_inf.mpr this
    rw [this]
    simp [st.clauseDb.toPropTerm_delClause_eq _ _ hGet]
  have hPogDefs : st'.pogDefsTerm = st.pogDefsTerm :=
    st.clauseDb.toPropTermSub_delClause_of_not_mem hMem
  have pfs' := { pfs with
    pogDefs_in_clauseDb := fun idx h => by
      refine st.clauseDb.contains_delClause _ _ |>.mpr ⟨pfs.pogDefs_in_clauseDb idx h, ?_⟩
      intro hEq
      exact hMem (hEq.symm ▸ h)
    equivalent_clauseDb := hDb ▸ pfs.equivalent_clauseDb
    clauseDb_semVars_sub := hDb ▸ pfs.clauseDb_semVars_sub
    pogDefsTerm_semVars_sub := hPogDefs ▸ pfs.pogDefsTerm_semVars_sub
    equivalent_lits := hPogDefs ▸ pfs.equivalent_lits
    uep_pogDefsTerm := hPogDefs ▸ pfs.uep_pogDefsTerm
  }
  set (σ := State) ⟨st', pfs'⟩

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
    pogDefs
    pog := pog'
    depVars := st.depVars.insert x union
    root := st.root
  }
  have pfs' := sorry
  set (σ := State) ⟨st', pfs'⟩

def addPogDefClause (db₀ : ClauseDb ClauseIdx) (pd₀ : HashSet ClauseIdx)
    (idx : ClauseIdx) (C : IClause) (h : ∀ idx, idx ∈ pd₀.toFinset → db₀.contains idx) :
    Except CheckerError { p : ClauseDb ClauseIdx × HashSet ClauseIdx //
      p.1.toPropTerm = db₀.toPropTerm ⊓ C.toPropTerm ∧
      p.1.toPropTermSub (· ∈ p.2.toFinset) = db₀.toPropTermSub (· ∈ pd₀.toFinset) ⊓ C.toPropTerm ∧
      ∀ idx, idx ∈ p.2.toFinset → p.1.contains idx } := do
  let ⟨db, hAdd, hNContains, hDb⟩ ← addClause db₀ idx C
  let pd := pd₀.insert idx

  have hMem : idx ∈ pd.toFinset := by simp
  have hContainsTrans : ∀ {idx}, db₀.contains idx → db.contains idx := fun h => by
    rw [hAdd]
    exact db₀.contains_addClause _ _ _ |>.mpr (Or.inl h)
  have hContains : db.contains idx := by
    rw [hAdd]
    exact db₀.contains_addClause _ _ _ |>.mpr (Or.inr rfl)
  have hHelper : db₀.toPropTermSub (· ∈ pd.toFinset) = db₀.toPropTermSub (· ∈ pd₀.toFinset) := by
    apply db₀.toPropTermSub_subset_eq (fun x hMem => by simp; exact Or.inl hMem)
    intro idx hMem hContains
    simp at hMem
    cases hMem with
    | inl hMem => exact hMem
    | inr h =>
      exfalso
      exact hNContains (h ▸ hContains)
  have hPd : db.toPropTermSub (· ∈ pd.toFinset) =
      db₀.toPropTermSub (· ∈ pd₀.toFinset) ⊓ C.toPropTerm := by
    rw [← hHelper, hAdd]
    exact db₀.toPropTermSub_addClause_eq _ hMem hNContains
  have hPdDb : ∀ idx, idx ∈ pd.toFinset → db.contains idx := by
    simp only [HashSet.toFinset_insert, Finset.mem_singleton, Finset.mem_union]
    intro _ h
    cases h with
    | inl hMem => exact hContainsTrans (h _ hMem)
    | inr h => exact h ▸ hContains

  return ⟨(db, pd), hDb, hPd, hPdDb⟩

def addSumClauses (db₀ : ClauseDb ClauseIdx) (pd₀ : HashSet ClauseIdx)
    (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (h : ∀ idx, idx ∈ pd₀.toFinset → db₀.contains idx) :
    Except CheckerError { p : ClauseDb ClauseIdx × HashSet ClauseIdx //
      p.1.toPropTerm = db₀.toPropTerm ⊓
        (.biImpl (.var x) (l₁.toPropTerm ⊔ l₂.toPropTerm)) ∧
      p.1.toPropTermSub (· ∈ p.2.toFinset) = db₀.toPropTermSub (· ∈ pd₀.toFinset) ⊓
        (.biImpl (.var x) (l₁.toPropTerm ⊔ l₂.toPropTerm)) ∧
      ∀ idx, idx ∈ p.2.toFinset → p.1.contains idx } := do
  let ⟨(db₁, pd₁), hDb₁, hPd₁, h⟩ ← addPogDefClause db₀ pd₀ idx     #[.mkNeg x, l₁, l₂] h
  let ⟨(db₂, pd₂), hDb₂, hPd₂, h⟩ ← addPogDefClause db₁ pd₁ (idx+1) #[.mkPos x, -l₁]    h
  let ⟨(db₃, pd₃), hDb₃, hPd₃, h⟩ ← addPogDefClause db₂ pd₂ (idx+2) #[.mkPos x, -l₂]    h
  have hDb := by
    rw [hDb₃, hDb₂, hDb₁]
    simp [IClause.toPropTerm, inf_assoc, PropTerm.disj_def_eq]
  have hPd := by
    rw [hPd₃, hPd₂, hPd₁]
    simp [IClause.toPropTerm, inf_assoc, PropTerm.disj_def_eq]
  return ⟨(db₃, pd₃), hDb, hPd, h⟩
  
def getDeps (st : PreState) (pfs : st.WF) (l : ILit) : Except CheckerError { D : HashSet Var //
    l.var ∈ st.allVars ∧
    (st.pog.toPropForm l).vars ⊆ D.toFinset } := do
  match h : st.depVars.find? l.var with
  | some D =>
    return ⟨D, st.depVars.contains_iff _ |>.mpr ⟨D, h⟩, pfs.depVars_pog _ _ h⟩
  | none => throw <| .unknownVar l.var
  
def ensureFreshVar (st : PreState) (x : Var) : Except CheckerError { _u : Unit //
    x ∉ st.allVars } := do
  if h : st.depVars.contains x then
    throw <| .duplicateExtVar x
  else
    return ⟨(), h⟩
    
def filterPogHints (st : PreState) (hints : Array ClauseIdx) :
    Except CheckerError { _u : Unit //
      ∀ idx, idx ∈ hints.data → idx ∈ st.pogDefs' } := do
  return ⟨(), sorry⟩
  
def addDisjToPog (g : Pog) (x : Var) (l₁ l₂ : ILit) : Except CheckerError { g' : Pog //
    g.addDisj x l₁ l₂ = .ok g' } :=
  match g.addDisj x l₁ l₂ with
  | .ok g' => pure ⟨g', rfl⟩
  | .error e => throw <| .graphUpdateError e
  
def addSum (idx : ClauseIdx) (x : Var) (l₁ l₂ : ILit) (hints : Array ClauseIdx) :
    CheckerM Unit := do
  let ⟨st, pfs⟩ ← get

  -- Check that added variable is fresh.
  let ⟨_, hX⟩ ← ensureFreshVar st x

  -- Check that variables are known and compute their dependencies.
  let ⟨D₁, hL₁, hD₁⟩ ← getDeps st pfs l₁
  let ⟨D₂, hL₂, hD₂⟩ ← getDeps st pfs l₂

  let ⟨pog', hPog⟩ ← addDisjToPog st.pog x l₁ l₂

  -- Check that POG defs imply that the children have no models in common.
  let ⟨_, hHints⟩ ← filterPogHints st hints
  -- NOTE: Important that this be done before adding clauses, for linearity.
  let ⟨_, hImp⟩ ← checkImpliedWithHints st.clauseDb #[-l₁, -l₂] hints

  let ⟨(db', pd'), hDb, hPd, pogDefs_in_clauseDb⟩ ←
    addSumClauses st.clauseDb st.pogDefs idx x l₁ l₂ pfs.pogDefs_in_clauseDb

  let st' := { st with
    clauseDb := db'
    pogDefs := pd'
    pog := pog'
    depVars := st.depVars.insert x (D₁.union D₂)
  }

  have hDisjoint : st.pogDefsTerm ⊓ l₁.toPropTerm ⊓ l₂.toPropTerm ≤ ⊥ := by
    have : st.pogDefsTerm ≤ st.clauseDb.toPropTermSub (· ∈ hints.data) :=
      st.clauseDb.toPropTermSub_subset hHints
    rw [inf_assoc, ← le_himp_iff]
    have := le_trans this hImp
    simp [IClause.toPropTerm] at this
    simp [this]

  -- Variable stuff
  have : db'.toPropTerm.semVars = st.clauseDb.toPropTerm.semVars ∪ {x} := sorry
  have : st'.allVars = st.allVars.insert x := by
    sorry

  have pfs' := {
    pogDefs_in_clauseDb
    depVars_pog := sorry
    partitioned := by
      intro y
      by_cases hEq : x = y
      . rw [st.pog.toPropForm_addDisj _ _ _ _ (hEq ▸ hPog)] 
        refine addDisj_partitioned st.pogDefsTerm l₁.toPropTerm l₂.toPropTerm _ _ ?sub
          pfs.uep_pogDefsTerm hDisjoint (pfs.equivalent_lits l₁) (pfs.equivalent_lits l₂)
          (pfs.partitioned' l₁) (pfs.partitioned' l₂)
        simp [hL₂]
      . rw [st.pog.toPropForm_addDisj_of_ne _ _ _ _ _ hPog hEq]
        exact pfs.partitioned y
    clauseDb_semVars_sub := sorry
    pogDefsTerm_semVars_sub := sorry
    inputCnf_semVars_sub := sorry
    equivalent_clauseDb := by -- TODO 1
      apply pfs.equivalent_clauseDb.trans
      rw [hDb]
      -- strategy:
      apply PropTerm.equivalentOver_def_ext <;> sorry
      -- with X := st.allVars
      -- use clauseDb_semVars_sub for first obligation
      -- use l₁,l₂ ∈ allVars for the second
      -- use freshness check for the third
      -- reduce to inputVars using subset proof (argh)
    pog_vars := sorry
    uep_pogDefsTerm := sorry
    equivalent_lits := sorry -- TODO 2
  }
  set (σ := State) ⟨st', pfs'⟩

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