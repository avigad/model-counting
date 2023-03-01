import Mathlib.Tactic.Linarith

import ProofChecker.Data.HashMap.Lemmas
import ProofChecker.Data.HashSet
import ProofChecker.Model.ToMathlib
import ProofChecker.Model.PropTerm

/-! Literals -/

def ILit := Int

namespace ILit

def mkPos (x : Nat) : ILit :=
  Int.ofNat x

def mkNeg (x : Nat) : ILit :=
  -Int.ofNat x

def var : ILit → Nat :=
  Int.natAbs

def polarity (l : ILit) : Bool :=
  (0 : Int) < l

def negate : ILit → ILit :=
  Int.neg

instance : Neg ILit := ⟨negate⟩

instance : BEq ILit :=
  inferInstanceAs (BEq Int)

instance : ToString ILit where
  toString l := if l.polarity then s!"{l.var}" else s!"-{l.var}"

instance : DecidableEq ILit := inferInstanceAs (DecidableEq Int)

instance : Repr ILit := inferInstanceAs (Repr Int)

/-! Theorems about `ILit` -/

@[simp]
theorem var_mkPos (x : Nat) : var (mkPos x) = x :=
  Int.natAbs_ofNat x

@[simp]
theorem var_mkNeg (x : Nat) : var (mkNeg x) = x := by
  simp [var, mkNeg]

@[simp]
theorem var_negate (l : ILit) : (-l).var = l.var := by
  simp only [var, Neg.neg, negate]
  apply Int.natAbs_neg

theorem polarity_negate (l : ILit) : l ≠ (0 : Int) → (-l).polarity = !l.polarity := by
  suffices ∀ (l: Int), l ≠ 0 → ¬(0 < -l ↔ 0 < l) by
    simp only [polarity, Neg.neg, negate, Bool.eq_bnot_to_not_eq]
    intro hNe h
    rw [Bool.decide_eq] at h
    apply this l hNe h
  intro l hNe h
  exact hNe (Int.eq_zero_of_lt_neg_iff_lt l h)

@[ext]
theorem ext {l₁ l₂ : ILit} : l₁.var = l₂.var → l₁.polarity = l₂.polarity → l₁ = l₂ := by
  /- Strip type alias. -/
  suffices ∀ {l₁ l₂ : Int}, var l₁ = var l₂ → polarity l₁ = polarity l₂ → l₁ = l₂ from
    this
  intro l₁ l₂ h₁ h₂
  cases Int.natAbs_eq_natAbs_iff.mp h₁
  . assumption
  next h =>
    rw [polarity, polarity, h, Bool.decide_eq] at h₂
    have : l₂ = 0 := Int.eq_zero_of_lt_neg_iff_lt l₂ h₂
    simp [this, h]

def toPropForm (l : ILit) : PropForm Nat :=
  if l.polarity then .var l.var else .neg (.var l.var)

def toPropTerm (l : ILit) : PropTerm Nat :=
  if l.polarity then .var l.var else (.var l.var)ᶜ

@[simp]
theorem mk_toPropForm (l : ILit) : ⟦l.toPropForm⟧ = l.toPropTerm := by
  dsimp [toPropForm, toPropTerm]
  cases l.polarity <;> simp

open PropTerm

theorem satisfies_iff {τ : PropAssignment Nat} {l : ILit} :
    τ ⊨ l.toPropTerm ↔ τ l.var = l.polarity := by
  dsimp [toPropTerm, var, polarity]
  aesop

theorem satisfies_set [DecidableEq ν] (τ : PropAssignment Nat) (l : ILit) :
    τ.set l.var l.polarity ⊨ l.toPropTerm := by
  simp [satisfies_iff, τ.set_get]

end ILit

/-! Clauses -/

abbrev IClause := Array ILit

namespace IClause

def vars (C : IClause) : HashSet Nat :=
  C.foldl (init := .empty Nat) fun acc l => acc.insert l.var

instance : BEq IClause :=
  inferInstanceAs (BEq IClause)

instance : ToString IClause where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

/-! Theorems about `IClause` -/

def toPropTerm : IClause → PropTerm Nat :=
  Array.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ)

end IClause

/-! CNF -/

abbrev ICnf := Array IClause

namespace ICnf

def vars (C : ICnf) : HashSet Nat :=
  C.foldl (init := .empty Nat) fun acc C => acc.union C.vars

instance : ToString ICnf where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

/-! Theorems about `ICnf` -/

def toPropTerm : ICnf → PropTerm Nat :=
  Array.foldr (init := ⊤) (fun l φ => l.toPropTerm ⊓ φ)

end ICnf

/-! Partial assignments -/

/-- A partial assignment to propositional variables. -/
-- TODO: Using `HashMap` for this is cache-inefficient but I don't have time to verify better
-- structures rn
abbrev PartPropAssignment := HashMap Nat Bool

namespace PartPropAssignment

/-- Interpret the assignment (x ↦ ⊤, y ↦ ⊥) as x ∧ ¬y, for example. -/
def toPropTerm (τ : PartPropAssignment) : PropTerm Nat :=
  τ.fold (init := .tr) fun acc x v => acc.conj <| if v then .var x else .neg (.var x)

end PartPropAssignment

namespace IClause

/-- Reduces a clause by a partial assignment. Returns `none` if it became satisfied,
otherwise `some C'` where `C'` is the reduced clause. -/
def reduce (C : IClause) (τ : PartPropAssignment) : Option IClause :=
  C.foldlM (init := #[]) fun acc l =>
    match τ.find? l.var with
    | some v => if v == l.polarity then none else acc
    | none => some <| acc.push l

/-- When `C` is not a tautology, return the smallest assignment falsifying it. When it is, return
an undetermined assignment. -/
def toFalsifyingAssignment (C : IClause) : PartPropAssignment :=
  C.foldr (init := .empty) fun l acc => acc.insert l.var !l.polarity

-- theorem toPropTerm_negToPartPropAssignment (C : IClause) (h : ¬C.toClause.isTautology) :
--     C.toFalsifyingAssignment.toPropTerm = (C.toClause.toPropTerm)ᶜ := by
--   sorry

end IClause