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

def ofICnf (cnf : ICnf) : ClauseDb Nat :=
  let (db, _) : ClauseDb Nat × Nat :=
    cnf.foldl (init := (empty, 1)) fun (db, idx) C =>
      (db.addClause idx C, idx + 1)
  db

/-- Propagates units starting from the given assignment. The clauses in `hints` are expected to become
unit in the order provided. Returns the extended assignment, or `none` if a contradiction was found. -/
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

theorem getClause_eq_some (db : ClauseDb α) (idx : α) (C : IClause) :
    db.getClause idx = some C ↔ db.clauses.find? idx = some (C, false) := by
  simp [getClause]

theorem contains_iff_getClause_eq_some (db : ClauseDb α) (idx : α) :
    db.contains idx ↔ ∃ C, db.getClause idx = some C := by
  simp [contains, Option.isSome_iff_exists, db.clauses.contains_iff_find?_eq]

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

def toPropTerm (db : ClauseDb α) : PropTerm Var :=
  db.fold (init := .tr) fun acc _ C => acc ⊓ C.toPropTerm

theorem toPropTerm_of_getClause_eq_some (db : ClauseDb α) (idx : α) (C : IClause)
    : db.getClause idx = some C → ∃ φ, db.toPropTerm = φ ⊓ C.toPropTerm := by
  intro h
  have ⟨φ, hφ⟩ := db.fold_of_getClause_eq_some_of_comm idx C
    (init := PropTerm.tr) (f := fun acc _ C => acc ⊓ C.toPropTerm)
    h ?comm
  case comm =>
    intro φ _ C₁ _ C₂
    dsimp
    ac_rfl -- whoa this works?!
  use φ
  simp [toPropTerm, hφ]

open PropTerm in
theorem satisfies_toPropTerm (db : ClauseDb α) (σ : PropAssignment Var) :
    σ ⊨ db.toPropTerm ↔ ∀ idx C, db.getClause idx = some C → σ ⊨ C.toPropTerm :=
  ⟨mp, mpr⟩
where
  mp := fun h idx C hC => by
    have ⟨φ, hφ⟩ := toPropTerm_of_getClause_eq_some db idx C hC
    rw [hφ, satisfies_conj] at h
    tauto

  mpr := fun h => by
    dsimp [toPropTerm]
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ idx (C, deleted) hφ hIdx
    dsimp
    split
    next => assumption
    next hDel =>
      rw [satisfies_conj]
      refine ⟨by assumption, ?_⟩
      apply h idx
      rw [getClause, hIdx]
      simp [*]

theorem toPropTerm_of_getClause (db : ClauseDb α) (idx : α) (C : IClause) :
    db.getClause idx = some C → db.toPropTerm ≤ C.toPropTerm := by
  intro h
  apply PropTerm.entails_ext.mpr
  simp only [satisfies_toPropTerm]
  tauto

open PropTerm in
theorem toPropTerm_addClause (db : ClauseDb α) (idx : α) (C : IClause) :
    (db.toPropTerm ⊓ C.toPropTerm) ≤ (db.addClause idx C).toPropTerm := by
  apply PropTerm.entails_ext.mpr
  simp only [satisfies_conj, satisfies_toPropTerm]
  intro τ h idx' C' hC'
  by_cases hEq : idx = idx'
  . rw [hEq, getClause_addClause] at hC'
    cases hC'
    tauto
  . apply h.left idx'
    exact getClause_addClause_of_ne _ _ _ _ hEq ▸ hC'

open PropTerm in
theorem toPropTerm_addClause_of_contains (db : ClauseDb α) (idx : α) (C : IClause) :
    !db.contains idx →
    (db.addClause idx C).toPropTerm = db.toPropTerm ⊓ C.toPropTerm := by
  intro h
  refine PropTerm.entails.antisymm ?_ (toPropTerm_addClause db idx C)
  apply PropTerm.entails_ext.mpr
  simp only [satisfies_conj, satisfies_toPropTerm]
  intro τ hτ
  refine ⟨?_, hτ idx C (getClause_addClause _ _ _)⟩
  intro idx' C' hC'
  apply hτ idx'
  by_cases hEq : idx = idx'
  . rw [hEq, (contains_iff_getClause_eq_some _ _).mpr ⟨C', hC'⟩] at h
    contradiction
  . rw [getClause_addClause_of_ne _ _ _ _ hEq]
    exact hC'

theorem toPropTerm_delClause (db : ClauseDb α) (idx : α) :
    db.toPropTerm ≤ (db.delClause idx).toPropTerm := by
  apply PropTerm.entails_ext.mpr
  simp only [satisfies_toPropTerm]
  intro τ h idx' C' hC'
  by_cases hEq : idx = idx'
  . rw [hEq, getClause_delClause] at hC'
    contradiction
  . rw [getClause_delClause_of_ne _ _ _ hEq] at hC'
    exact h idx' C' hC'

theorem toPropTerm_ofICnf (cnf : ICnf) : (ofICnf cnf).toPropTerm = cnf.toPropTerm := by
  sorry -- Array.foldl_eq_foldl_data ? or Array.foldl_induction ?

theorem entails_of_unitProp (db : ClauseDb α) (τ : PartPropAssignment) (hints : Array α) :
    db.unitPropWithHints τ hints |>.isContradiction → db.toPropTerm ≤ τ.toPropTermᶜ :=
  sorry

end ClauseDb