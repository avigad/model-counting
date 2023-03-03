import Mathlib.Tactic.Linarith

import ProofChecker.Data.HashMap.Lemmas
import ProofChecker.Data.HashSet
import ProofChecker.Model.ToMathlib
import ProofChecker.Model.PropTerm

abbrev Var := PNat

namespace Var

instance : ToString Var where
  toString x := toString x.val

instance : Hashable Var where
  hash v := hash v.val

end Var

/-! Literals -/

def ILit := { i : Int // i ≠ 0 }
  deriving DecidableEq, Repr

namespace ILit

def mkPos (x : Var) : ILit :=
  ⟨Int.ofNat x.val, by simp⟩

def mkNeg (x : Var) : ILit :=
  ⟨-Int.ofNat x.val, by simp⟩

def var (l : ILit) : Var :=
  ⟨Int.natAbs l.val, Int.natAbs_pos.mpr l.property⟩

def polarity (l : ILit) : Bool :=
  (0 : Int) < l.val

def negate (l : ILit) : ILit :=
  ⟨-l.val, Int.neg_ne_zero.mpr l.property⟩

instance : Neg ILit := ⟨negate⟩

instance : ToString ILit where
  toString l := if l.polarity then s!"{l.var}" else s!"-{l.var}"

/-! Theorems about `ILit` -/

@[simp]
theorem var_mkPos (x :  Var) : var (mkPos x) = x :=
  Subtype.ext (Int.natAbs_ofNat x.val)

@[simp]
theorem var_mkNeg (x : Var) : var (mkNeg x) = x := by
  apply Subtype.ext
  simp [var, mkNeg]
  rfl

@[simp]
theorem var_negate (l : ILit) : (-l).var = l.var := by
  simp only [var, Neg.neg, negate]
  apply Subtype.ext
  apply Int.natAbs_neg

theorem polarity_eq {l₁ l₂ : ILit} :
    l₁.polarity = l₂.polarity ↔ ((0 : Int) < l₁.val ↔ (0 : Int) < l₂.val) := by
  simp [polarity]

theorem polarity_negate (l : ILit) : (-l).polarity = !l.polarity := by
  rw [Bool.eq_bnot_to_not_eq, polarity_eq]
  intro hEq
  exact l.property (Int.eq_zero_of_lt_neg_iff_lt _ hEq)

@[ext]
theorem ext {l₁ l₂ : ILit} : l₁.var = l₂.var → l₁.polarity = l₂.polarity → l₁ = l₂ := by
  /- Strip type alias. -/
  suffices ∀ {l₁ l₂ : Int}, l₁.natAbs = l₂.natAbs → (0 < l₁ ↔ 0 < l₂) → l₁ = l₂ by
    intro h₁ h₂
    apply Subtype.ext
    apply this
    . exact Subtype.mk_eq_mk.mp h₁
    . exact polarity_eq.mp h₂
  intro l₁ l₂ h₁ h₂
  cases Int.natAbs_eq_natAbs_iff.mp h₁
  . assumption
  next h =>
    rw [h] at h₂
    have : l₂ = 0 := Int.eq_zero_of_lt_neg_iff_lt l₂ h₂
    simp [this, h]

def toPropForm (l : ILit) : PropForm Var :=
  if l.polarity then .var l.var else .neg (.var l.var)

def toPropTerm (l : ILit) : PropTerm Var :=
  if l.polarity then .var l.var else (.var l.var)ᶜ

@[simp]
theorem mk_toPropForm (l : ILit) : ⟦l.toPropForm⟧ = l.toPropTerm := by
  dsimp [toPropForm, toPropTerm]
  cases l.polarity <;> simp

open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {l : ILit} :
    τ ⊨ l.toPropTerm ↔ τ l.var = l.polarity := by
  dsimp [toPropTerm, var, polarity]
  aesop

theorem satisfies_set [DecidableEq ν] (τ : PropAssignment Var) (l : ILit) :
    τ.set l.var l.polarity ⊨ l.toPropTerm := by
  simp [satisfies_iff, τ.set_get]

end ILit

/-! Clauses -/

abbrev IClause := Array ILit

namespace IClause

def vars (C : IClause) : HashSet Var :=
  C.foldr (init := .empty Var) fun l acc => acc.insert l.var

instance : BEq IClause :=
  inferInstanceAs (BEq IClause)

instance : ToString IClause where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

/-! Theorems about `IClause` -/

def toPropTerm : IClause → PropTerm Var :=
  Array.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ)
  
open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {C : IClause} :
    τ ⊨ C.toPropTerm ↔ ∃ l ∈ C.data, τ ⊨ l.toPropTerm := by
  rw [toPropTerm, Array.foldr_eq_foldr_data]
  induction C.data <;> simp_all

end IClause

/-! CNF -/

abbrev ICnf := Array IClause

namespace ICnf

def vars (C : ICnf) : HashSet Var :=
  C.foldr (init := .empty Var) fun C acc => acc.union C.vars

instance : ToString ICnf where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

/-! Theorems about `ICnf` -/

def toPropTerm : ICnf → PropTerm Var :=
  Array.foldr (init := ⊤) (fun l φ => l.toPropTerm ⊓ φ)
  
open PropTerm
  
theorem satisfies_iff {τ : PropAssignment Var} {φ : ICnf} :
    τ ⊨ φ.toPropTerm ↔ ∀ C ∈ φ.data, τ ⊨ C.toPropTerm := by
  rw [toPropTerm, Array.foldr_eq_foldr_data]
  induction φ.data <;> simp_all

end ICnf

/-! Partial assignments -/

/-- A partial assignment to propositional variables. -/
-- TODO: Using `HashMap` for this is cache-inefficient but I don't have time to verify better
-- structures rn
abbrev PartPropAssignment := HashMap Var Bool

namespace PartPropAssignment

/-- Interpret the assignment (x ↦ ⊤, y ↦ ⊥) as x ∧ ¬y, for example. -/
def toPropTerm (τ : PartPropAssignment) : PropTerm Var :=
  τ.fold (init := ⊤) fun acc x v => acc ⊓ if v then .var x else (.var x)ᶜ

end PartPropAssignment

namespace IClause

/-- Reduces a clause by a partial assignment. Returns `none` if it became satisfied,
otherwise `some C'` where `C'` is the reduced clause. -/
def reduce (C : IClause) (τ : PartPropAssignment) : Option IClause :=
  C.foldlM (init := #[]) fun acc l =>
    match τ.find? l.var with
    | some v => if v == l.polarity then none else acc
    | none => some <| acc.push l
    
-- TODO: What's the `reduce` theorem?

/-- When `C` is not a tautology, return the smallest assignment falsifying it. When it is, return
an undetermined assignment. -/
def toFalsifyingAssignment (C : IClause) : PartPropAssignment :=
  C.foldr (init := .empty) fun l acc => acc.insert l.var !l.polarity

theorem toPropTerm_toFalsifyingAssignment (C : IClause) :
    C.toFalsifyingAssignment.toPropTerm = C.toPropTermᶜ := by
  sorry

end IClause