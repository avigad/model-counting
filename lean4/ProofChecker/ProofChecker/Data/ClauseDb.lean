import ProofChecker.Model.PropForm
import ProofChecker.Model.PropVars

import ProofChecker.Data.HashMap.Extra
import ProofChecker.Data.ICnf

/-! Clause database together with some (TBD provably correct) methods. For example, we can conclude
that if a clause follows from the current database by unit propagation, then it is implied by the
database's interpretation as a propositional formula. -/

/-- A stateful clause database, i.e. a dynamically modifiable CNF, for use in poly-time proof
checkers such as for LRAT. It uses in-place data structures, so should be used linearly.

(Persistent structures do not seem immediately helpful as linear formats do not backtrack.)

In `ClauseDb α`, `α` is the type of clause indices. -/
structure ClauseDb (α : Type) [BEq α] [Hashable α] where
  /-- Each clause is stored together with a flag indicating whether it has been deleted.
  Deleted clauses are logically not in the database. -/
  clauses : HashMap α (IClause × Bool) := {}

namespace HashMap

variable [BEq α] [Hashable α]

def mapOne (m : HashMap α β) (idx : α) (f : β → β) : HashMap α β :=
  match m.find? idx with
  | some b => m.insert idx (f b)
  | none => m

end HashMap

inductive UnitPropResult (α : Type) where
  | contradiction
  /-- The hint did not become unit. -/
  | hintNotUnit (hint : α)
  /-- The hint points at a nonexistent clause. -/
  | hintNonexistent (hint : α)
  | extended (τ : PartPropAssignment)

namespace UnitPropResult

def isContradiction (r : UnitPropResult α) : Bool :=
  r matches contradiction

end UnitPropResult

namespace ClauseDb

variable {α : Type} [BEq α] [Hashable α]

instance [ToString α] : ToString (ClauseDb α) where
  toString db := toString db.clauses.toList

def empty : ClauseDb α := { clauses := .empty }

def fold (db : ClauseDb α) (f : β → α → IClause → β) (init : β) : β :=
  db.clauses.fold (init := init) fun acc idx (C, deleted) =>
    if deleted then acc else f acc idx C

def foldM [Monad m] (db : ClauseDb α) (f : β → α → IClause → m β) (init : β) : m β :=
  db.clauses.foldM (init := init) fun acc idx (C, deleted) =>
    if deleted then pure acc else f acc idx C

def addClause (db : ClauseDb α) (idx : α) (C : IClause) : ClauseDb α :=
  { db with clauses := db.clauses.insert idx (C, false) }

def delClause (db : ClauseDb α) (idx : α) : ClauseDb α :=
  { db with clauses := db.clauses.mapOne idx fun (C, _) => (C, true) }

def getClause (db : ClauseDb α) (idx : α) : Option IClause :=
  db.clauses.find? idx |>.bind (fun (C, deleted) => if deleted then none else C)

def contains (db : ClauseDb α) (idx : α) : Bool :=
  db.getClause idx |>.isSome

/-- Initialize a clause database from a CNF array. -/
def ofICnf (cnf : ICnf) : ClauseDb Nat :=
  let (db, _) := cnf.foldl (init := (empty, 1)) fun (db, idx) C =>
    (db.addClause idx C, idx + 1)
  db

/-- Propagate units starting from the given assignment. The clauses in `hints` are expected
to become unit in the order provided. Return the extended assignment, or `none` if a contradiction
was found. See `unitPropWithHintsDep` for a certified version. -/
def unitPropWithHints (db : ClauseDb α) (τ : PartPropAssignment) (hints : Array α)
    : UnitPropResult α := Id.run do
  let mut τ := τ
  for hint in hints do
    let some C := db.getClause hint
      | return .hintNonexistent hint
    match C.reduce τ with
    | some #[u] => τ := τ.insert u.var u.polarity
    | some #[] => return .contradiction
    | _ => return .hintNotUnit hint
  return .extended τ

/-! Theorems about `ClauseDb` -/

variable [LawfulBEq α] [HashMap.LawfulHashable α]

/-! `getClause` -/

theorem getClause_eq_some (db : ClauseDb α) (idx : α) (C : IClause) :
    db.getClause idx = some C ↔ db.clauses.find? idx = some (C, false) := by
  simp [getClause]

@[simp]
theorem getClause_empty (idx : α) : (empty : ClauseDb α).getClause idx = none := by
  simp [getClause, empty]

theorem contains_iff_getClause_eq_some (db : ClauseDb α) (idx : α) :
    db.contains idx ↔ ∃ C, db.getClause idx = some C := by
  simp [contains, Option.isSome_iff_exists, db.clauses.contains_iff]

theorem not_contains_empty (idx : α) : ¬(empty : ClauseDb α).contains idx := by
  rw [contains_iff_getClause_eq_some]
  simp

theorem getClause_addClause (db : ClauseDb α) (idx : α) (C : IClause) :
    (db.addClause idx C).getClause idx = some C := by
  dsimp [getClause, addClause]
  rw [HashMap.find?_insert _ _ (LawfulBEq.rfl)]
  simp

theorem getClause_addClause_of_ne (db : ClauseDb α) (idx idx' : α) (C : IClause) :
    idx ≠ idx' → (db.addClause idx C).getClause idx' = db.getClause idx' := by
  intro h
  dsimp [addClause, getClause]
  rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne idx idx' |>.mpr h)]

theorem getClause_delClause (db : ClauseDb α) (idx : α) :
    (db.delClause idx).getClause idx = none := by
  dsimp [getClause, delClause, HashMap.mapOne]
  split
  next =>
    rw [HashMap.find?_insert _ _ (LawfulBEq.rfl)]
    simp
  next h =>
    simp [h]

theorem getClause_delClause_of_ne (db : ClauseDb α) (idx idx' : α) :
    idx ≠ idx' → (db.delClause idx).getClause idx' = db.getClause idx' := by
  intro h
  dsimp [getClause, delClause, HashMap.mapOne]
  split
  next =>
    rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr h)]
  next => rfl

/-! `fold` -/

theorem fold_of_getClause_eq_some_of_comm (db : ClauseDb α) (idx : α) (C : IClause)
    (f : β → α → IClause → β) (init : β) :
    db.getClause idx = some C →
    (∀ b a₁ C₁ a₂ C₂, f (f b a₁ C₁) a₂ C₂ = f (f b a₂ C₂) a₁ C₁) →
    ∃ b, db.fold f init = f b idx C := by
  intro h hComm
  rw [getClause_eq_some] at h
  have ⟨b, hb⟩ := db.clauses.fold_of_mapsTo_of_comm (init := init)
    (f := fun acc idx (C, deleted) => if deleted then acc else f acc idx C)
    h (by aesop)
  use b
  simp [fold, hb]

/-! `toPropTermSub` -/

open Classical PropTerm

/-- Interpret the conjunction of a subset of the clauses as a Boolean function. -/
noncomputable def toPropTermSub (db : ClauseDb α) (idxs : Set α) : PropTerm Var :=
  db.fold (init := ⊤) fun acc idx C => if idx ∈ idxs then acc ⊓ C.toPropTerm else acc

theorem toPropTermSub_of_getClause_eq_some (db : ClauseDb α) :
    idx ∈ idxs → db.getClause idx = some C → db.toPropTermSub idxs ≤ C.toPropTerm := by
  intro hMem hGet
  have ⟨φ, hφ⟩ := db.fold_of_getClause_eq_some_of_comm idx C
    (init := ⊤) (f := fun acc idx C => if idx ∈ idxs then acc ⊓ C.toPropTerm else acc)
    hGet ?comm
  case comm =>
    intros
    dsimp
    split_ifs <;> ac_rfl
  apply PropTerm.entails_ext.mpr
  rw [toPropTermSub, hφ]
  simp [hMem]

theorem satisfies_toPropTermSub (db : ClauseDb α) (idxs : Set α) (σ : PropAssignment Var) :
    σ ⊨ db.toPropTermSub idxs ↔ ∀ idx ∈ idxs, ∀ C, db.getClause idx = some C → σ ⊨ C.toPropTerm :=
  ⟨mp, mpr⟩
where
  mp := fun h idx hMem C hGet =>
    entails_ext.mp (toPropTermSub_of_getClause_eq_some db hMem hGet) _ h

  mpr := fun h => by
    dsimp [toPropTermSub]
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ idx (C, deleted) hφ hFind
    dsimp
    split_ifs <;> try assumption
    next hDel hMem =>
      rw [satisfies_conj]
      refine ⟨by assumption, ?_⟩
      apply h idx hMem
      simp [getClause, hFind, hDel]

@[simp]
theorem toPropTermSub_empty (idxs : Set α) : (empty : ClauseDb α).toPropTermSub idxs = ⊤ := by
  ext τ
  simp [satisfies_toPropTermSub]

@[simp]
theorem toPropTermSub_emptySet (db : ClauseDb α) : db.toPropTermSub ∅ = ⊤ := by
  ext τ
  aesop (add norm satisfies_toPropTermSub)

theorem toPropTermSub_subset (db : ClauseDb α) :
    idxs ⊆ idxs' → db.toPropTermSub idxs' ≤ db.toPropTermSub idxs := by
  intro hSub
  apply entails_ext.mpr
  aesop (add norm satisfies_toPropTermSub)

theorem toPropTermSub_addClause (db : ClauseDb α) (idxs : Set α) (idx : α) (C : IClause) :
    db.toPropTermSub idxs ⊓ C.toPropTerm ≤ (db.addClause idx C).toPropTermSub idxs := by
  apply entails_ext.mpr
  simp only [satisfies_conj, satisfies_toPropTermSub]
  intro τ h idx' C' hMem' hGet'
  by_cases hEq : idx = idx'
  . rw [hEq, getClause_addClause] at hGet'
    cases hGet'
    tauto
  . apply h.left idx' C' hMem'
    exact getClause_addClause_of_ne _ _ _ _ hEq ▸ hGet'

theorem toPropTermSub_addClause' (db : ClauseDb α) (C : IClause) :
    idx ∈ idxs → ¬db.contains idx →
    (db.addClause idx C).toPropTermSub idxs = db.toPropTermSub idxs ⊓ C.toPropTerm := by
  intro hMem hContains
  refine entails.antisymm ?_ (toPropTermSub_addClause db idxs idx C)
  refine entails_ext.mpr fun τ h => ?_
  simp only [satisfies_conj, satisfies_toPropTermSub] at h ⊢
  constructor
  case right =>
    apply h idx hMem
    apply getClause_addClause
  case left =>
    intro idx' hMem' C' hGet'
    apply h idx' hMem' C'
    by_cases hEq : idx = idx'
    . rw [hEq] at hContains
      have := contains_iff_getClause_eq_some _ _ |>.mpr ⟨C', hGet'⟩
      contradiction
    . rw [getClause_addClause_of_ne _ _ _ _ hEq]
      exact hGet'

theorem toPropTermSub_delClause (db : ClauseDb α) (idxs : Set α) (idx : α) :
    db.toPropTermSub idxs ≤ (db.delClause idx).toPropTermSub idxs := by
  apply PropTerm.entails_ext.mpr
  simp only [satisfies_toPropTermSub]
  intro τ h idx' hMem' C' hGet'
  by_cases hEq : idx = idx'
  . rw [hEq, getClause_delClause] at hGet'
    contradiction
  . rw [getClause_delClause_of_ne _ _ _ hEq] at hGet'
    exact h idx' hMem' C' hGet'

-- LATER(if needed): when idx ∉ idxs, (db.delClause idx).toPropTermSub idxs = db.toPropTermSub idxs

/-! `toPropTerm` -/

/-- Interpret the conjuction of all the clauses as a Boolean function. -/
noncomputable def toPropTerm (db : ClauseDb α) : PropTerm Var :=
  db.toPropTermSub Set.univ

theorem toPropTerm_of_getClause_eq_some (db : ClauseDb α) :
    db.getClause idx = some C → db.toPropTerm ≤ C.toPropTerm :=
  toPropTermSub_of_getClause_eq_some db (Set.mem_univ idx)

open PropTerm in
theorem satisfies_toPropTerm (db : ClauseDb α) (σ : PropAssignment Var) :
    σ ⊨ db.toPropTerm ↔ ∀ idx C, db.getClause idx = some C → σ ⊨ C.toPropTerm :=
  have ⟨mp, mpr⟩ := satisfies_toPropTermSub db Set.univ σ
  ⟨fun h idx C hGet => mp h idx (Set.mem_univ idx) C hGet,
   fun h => mpr (fun idx _ C hGet => h idx C hGet)⟩

@[simp]
theorem toPropTerm_empty : (empty : ClauseDb α).toPropTerm = ⊤ :=
  toPropTermSub_empty Set.univ

theorem toPropTerm_addClause (db : ClauseDb α) (idx : α) (C : IClause) :
    db.toPropTerm ⊓ C.toPropTerm ≤ (db.addClause idx C).toPropTerm :=
  toPropTermSub_addClause db Set.univ idx C

theorem toPropTerm_addClause' (db : ClauseDb α) (idx : α) (C : IClause) :
    ¬db.contains idx →
    (db.addClause idx C).toPropTerm = db.toPropTerm ⊓ C.toPropTerm :=
  toPropTermSub_addClause' db C (Set.mem_univ idx)

theorem toPropTerm_delClause (db : ClauseDb α) (idx : α) :
    db.toPropTerm ≤ (db.delClause idx).toPropTerm :=
  toPropTermSub_delClause db Set.univ idx

/-! `ofICnf` -/

theorem ofICnf_characterization (cnf : ICnf) :
    ¬(ofICnf cnf).contains 0 ∧
    (∀ i : Fin cnf.size, (ofICnf cnf).getClause (i + 1) = some cnf[i]) ∧
    (∀ i > cnf.size, ¬(ofICnf cnf).contains i) := by
  have ⟨h₁, h₂, h₃, _⟩ := cnf.foldl_induction
    (motive := fun (sz : Nat) (p : ClauseDb Nat × Nat) =>
      ¬p.1.contains 0 ∧
      (∀ i : Fin cnf.size, i < sz → p.1.getClause (i + 1) = some cnf[i]) ∧
      (∀ i > sz, ¬p.1.contains i) ∧
      p.2 = sz + 1)
    (init := (empty, 1))
    (f := fun (db, idx) C => (db.addClause idx C, idx + 1))
    (h0 := by simp [not_contains_empty])
    (hf := by
      intro sz (db, idx) ⟨ih₁, ih₂, ih₃, ih₄⟩
      dsimp at ih₄ ⊢
      simp only [ih₄, contains_iff_getClause_eq_some, and_true] at *
      refine ⟨?step₁, ?step₂, ?step₃⟩
      case step₁ =>
        have : sz.val + 1 ≠ 0 := Nat.succ_ne_zero _
        simp [getClause_addClause_of_ne _ _ _ _ this, ih₁]
      case step₂ =>
        intro i hLt
        by_cases hEq : sz.val = i.val
        . simp [hEq, getClause_addClause]
        . have : sz.val + 1 ≠ i.val + 1 := by simp [hEq]
          rw [getClause_addClause_of_ne _ _ _ _ this]
          apply ih₂
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hLt) (Ne.symm hEq)
      case step₃ =>
        intro i hGe
        have : sz.val + 1 ≠ i := Nat.ne_of_lt hGe
        rw [getClause_addClause_of_ne _ _ _ _ this]
        apply ih₃
        linarith)
  dsimp [ofICnf]
  exact ⟨h₁, fun i => h₂ i i.isLt, h₃⟩

theorem ofICnf_ext (cnf : ICnf) (C : IClause) :
    C ∈ cnf.data ↔ ∃ idx, (ofICnf cnf).getClause idx = some C := by
  have ⟨h₁, h₂, h₃⟩ := ofICnf_characterization cnf
  apply Iff.intro
  case mp =>
    intro h
    have ⟨i, h⟩ := Array.get_of_mem_data h
    use (i + 1)
    rw [← h]
    apply h₂
  case mpr =>
    intro ⟨idx, h⟩
    have hContains := contains_iff_getClause_eq_some _ _ |>.mpr ⟨C, h⟩
    have hPos : 0 < idx := by
      apply Nat.pos_of_ne_zero
      intro
      simp_all
    have hLt : idx - 1 < cnf.size := by
      suffices idx ≤ cnf.size by
        apply Nat.sub_lt_left_of_lt_add
        . apply Nat.succ_le_of_lt hPos
        . rw [add_comm]
          apply Nat.lt_succ_of_le this
      by_contra
      simp_all
    have hPred : idx - 1 + 1 = idx := Nat.succ_pred_eq_of_pos hPos
    have := h₂ ⟨idx - 1, hLt⟩
    simp only [hPred, h] at this
    cases this
    apply Array.get_mem_data

@[simp]
theorem toPropTerm_ofICnf (cnf : ICnf) : (ofICnf cnf).toPropTerm = cnf.toPropTerm := by
  ext τ
  simp only [ICnf.satisfies_iff, satisfies_toPropTerm, ofICnf_ext]
  aesop

/-! `unitPropWithHints` -/

inductive UnitPropResultDep {α : Type} [BEq α] [Hashable α]
    (db : ClauseDb α) (σ : PartPropAssignment) where
  | contradiction (h : db.toPropTerm ≤ σ.toPropTermᶜ)
  | extended (σ' : PartPropAssignment) (h : db.toPropTerm ⊓ σ.toPropTerm ≤ σ'.toPropTerm)
  /-- The hint `C` at index `idx` did not become unit under `σ`. -/
  | hintNotUnit (idx : α) (C : IClause) (σ : PartPropAssignment)
  /-- The hint points at a nonexistent clause. -/
  | hintNonexistent (idx : α)

open scoped PropTerm in
def unitPropWithHintsDep (db : ClauseDb α) (σ₀ : PartPropAssignment) (hints : Array α)
    : UnitPropResultDep db σ₀ := Id.run do
  let mut σ : {σ : PartPropAssignment // db.toPropTerm ⊓ σ₀.toPropTerm ≤ σ.toPropTerm } :=
    ⟨σ₀, inf_le_right⟩
  for hint in hints do
    match hGet : db.getClause hint with
    | none => return .hintNonexistent hint
    | some C =>
      have hDbσ₀ : db.toPropTerm ⊓ σ₀.toPropTerm ≤ C.toPropTerm ⊓ σ.val.toPropTerm :=
        le_inf (inf_le_of_left_le (toPropTerm_of_getClause_eq_some _ hGet)) σ.property
      match hRed : C.reduce σ.val with
      | some #[u] =>
        have : db.toPropTerm ⊓ σ₀.toPropTerm ≤
            PartPropAssignment.toPropTerm (σ.val.insert u.var u.polarity) := by
          have hU : db.toPropTerm ⊓ σ₀.toPropTerm ≤ u.toPropTerm := by
            have h := IClause.reduce_eq_some _ _ _ hRed
            conv at h => rhs; simp [IClause.toPropTerm]
            exact le_trans hDbσ₀ h
          refine PropTerm.entails_ext.mpr fun τ hτ => ?_
          have hU : τ ⊨ u.toPropTerm :=
            PropTerm.entails_ext.mp hU τ hτ
          have hσ : τ ⊨ σ.val.toPropTerm :=
            PropTerm.entails_ext.mp σ.property τ hτ
          rw [PartPropAssignment.satisfies_iff] at hσ ⊢
          intro x p hFind
          by_cases hEq : x = u.var
          next =>
            rw [hEq, HashMap.find?_insert _ _ LawfulBEq.rfl] at hFind
            rw [ILit.satisfies_iff] at hU
            simp_all
          next =>
            rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr (Ne.symm hEq))] at hFind
            exact hσ _ _ hFind
        σ := ⟨σ.val.insert u.var u.polarity, this⟩
      | some #[] =>
        have : db.toPropTerm ≤ σ₀.toPropTermᶜ := by
          have : C.toPropTerm ⊓ σ.val.toPropTerm ≤ ⊥ :=
            IClause.reduce_eq_some _ _ _ hRed
          rw [le_compl_iff_disjoint_right]
          exact disjoint_iff_inf_le.mpr (le_trans hDbσ₀ this)
        return .contradiction this
      | _ => return .hintNotUnit hint C σ.val
  return .extended σ.val σ.property

end ClauseDb