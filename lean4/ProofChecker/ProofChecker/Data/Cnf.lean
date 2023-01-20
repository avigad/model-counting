/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Data.List.Basic

import ProofChecker.PropTerm
import ProofChecker.PropVars

/-! Propositional formulas in CNF form. This is only intended for mathematical modelling.
For performant CNF see `ClauseDb`. -/

inductive Lit (ν : Type)
  | pos (x : ν)
  | neg (x : ν)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Lit

def toPropForm : Lit ν → PropForm ν
  | pos x => .var x
  | neg x => .neg (.var x)

def toPropTerm : Lit ν → PropTerm ν
  | pos x => .var x
  | neg x => (.var x)ᶜ

instance [ToString ν] : ToString (Lit ν) where
  toString l := toString l.toPropForm

def var : Lit ν → ν
  | pos x => x
  | neg x => x

def polarity : Lit ν → Bool
  | pos _ => true
  | neg _ => false

@[ext]
theorem ext {l₁ l₂ : Lit ν} : l₁.var = l₂.var → l₁.polarity = l₂.polarity → l₁ = l₂ := by
  cases l₁ <;> cases l₂ <;> simp [var, polarity]

open PropTerm

theorem satisfies_iff {τ : PropAssignment ν} {l : Lit ν} :
    τ ⊨ l.toPropTerm ↔ τ l.var = l.polarity := by
  cases l <;> simp [toPropTerm, var, polarity]

theorem satisfies_set [DecidableEq ν] (τ : PropAssignment ν) (l : Lit ν) :
    τ.set l.var l.polarity ⊨ l.toPropTerm := by
  simp [satisfies_iff, τ.set_get]

def negate : Lit ν → Lit ν
  | pos x => neg x
  | neg x => pos x

instance : Neg (Lit ν) := ⟨negate⟩

@[simp]
theorem var_neg (l : Lit ν) : (-l).var = l.var := by
  cases l <;> rfl

@[simp]
theorem polarity_neg (l : Lit ν) : (-l).polarity = !l.polarity := by
  cases l <;> rfl

end Lit

-- NOTE: Alternatively, could be Multiset or even Finset. Also, the `abbrev` is convenient but
-- should become a `def` if it start causing trouble.
abbrev Clause ν := List (Lit ν)

namespace Clause

def toPropForm : Clause ν → PropForm ν :=
  List.foldr (init := .fls) (fun l φ => .disj l.toPropForm φ)

def toPropTerm : Clause ν → PropTerm ν :=
  List.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ)

instance [ToString ν] : ToString (Clause ν) where
  toString C := toString C.toPropForm 

@[simp]
theorem toPropTerm_nil : toPropTerm ([] : Clause ν) = ⊥ := by
  simp [toPropTerm]

@[simp]
theorem toPropTerm_cons {C : Clause ν} : toPropTerm (l :: C) = l.toPropTerm ⊔ C.toPropTerm := by
  simp [toPropTerm]

@[simp]
theorem toPropTerm_append (C₁ C₂ : Clause ν) :
    toPropTerm (C₁ ++ C₂) = C₁.toPropTerm ⊔ C₂.toPropTerm := by
  conv => lhs; unfold toPropTerm
  rw [List.foldr_append, ← toPropTerm]
  induction C₁ with
  | nil => simp
  | cons _ _ ih => simp [ih, sup_assoc]

open PropTerm

theorem satisfies_iff {τ : PropAssignment ν} {C : Clause ν} :
    τ ⊨ C.toPropTerm ↔ ∃ l ∈ C, τ ⊨ l.toPropTerm := by
  induction C with
  | nil => simp [toPropTerm]
  | cons _ _ ih => simp [ih]

theorem toPropTerm_monotone {C₁ C₂ : Clause ν} : C₁ ⊆ C₂ → C₁.toPropTerm ≤ C₂.toPropTerm := by
  intro h
  apply PropTerm.entails_ext.mpr
  simp only [satisfies_iff]
  intro τ ⟨l, h₁⟩
  exact ⟨l, h h₁.left, h₁.right⟩

theorem satisfies_set [DecidableEq ν] (τ : PropAssignment ν) (C : Clause ν) (l : Lit ν) :
    l ∈ C → τ.set l.var l.polarity ⊨ C.toPropTerm :=
  fun h => satisfies_iff.mpr ⟨l, h, l.satisfies_set τ⟩

theorem satisfies_of_not_in [DecidableEq ν] (τ : PropAssignment ν) (C : Clause ν) (l : Lit ν) :
    l ∉ C → τ ⊨ C.toPropTerm → τ.set l.var (!l.polarity) ⊨ C.toPropTerm := by
  simp only [satisfies_iff]
  intro h ⟨l₁, hL₁C, hL₁⟩
  use l₁, hL₁C
  rw [l₁.satisfies_iff] at hL₁
  by_cases hVar : l.var = l₁.var
  . rw [hVar]
    have : l.polarity ≠ l₁.polarity := by
      intro h
      have : l = l₁ := Lit.ext hVar h
      cases this
      contradiction
    rw [ne_eq] at this
    simp [l₁.satisfies_iff, this]
  . simp only [l₁.satisfies_iff, τ.set_get_of_ne _ hVar, hL₁]

theorem satisfies_of_neg_not_in [DecidableEq ν] (τ : PropAssignment ν) (C : Clause ν) (l : Lit ν) :
    -l ∉ C → τ ⊨ C.toPropTerm → τ.set l.var l.polarity ⊨ C.toPropTerm :=
  fun h₁ h₂ => have := satisfies_of_not_in τ C (-l) h₁ h₂; by aesop

end Clause

-- Same representation considerations as on `Clause`.
abbrev CnfForm ν := List (Clause ν)

namespace CnfForm

def toPropForm : CnfForm ν → PropForm ν :=
  List.foldr (init := .tr) (fun C φ => .conj C.toPropForm φ)

def toPropTerm : CnfForm ν → PropTerm ν :=
  List.foldr (init := ⊤) (fun C φ => C.toPropTerm ⊓ φ)

instance [ToString ν] : ToString (CnfForm ν) where
  toString Cs := toString Cs.toPropForm

@[simp]
theorem toPropTerm_nil : toPropTerm ([] : CnfForm ν) = ⊤ := by
  simp [toPropTerm]

@[simp]
theorem toPropForm_cons (C : Clause ν) (F : CnfForm ν) :
    toPropTerm (C :: F) = C.toPropTerm ⊓ F.toPropTerm := by
  simp [toPropTerm]

@[simp]
theorem toPropTerm_append (F₁ F₂ : CnfForm ν) :
    toPropTerm (F₁ ++ F₂) = F₁.toPropTerm ⊓ F₂.toPropTerm := by
  conv => lhs; unfold toPropTerm
  rw [List.foldr_append, ← toPropTerm]
  induction F₁ with
  | nil => simp
  | cons _ _ ih => simp [ih, inf_assoc]

open PropTerm in
theorem satisfies_iff {τ : PropAssignment ν} {F : CnfForm ν} :
    τ ⊨ F.toPropTerm ↔ ∀ C ∈ F, τ ⊨ C.toPropTerm := by
  induction F with
  | nil => simp [toPropTerm, satisfies_tr]
  | cons _ _ ih => simp [ih]

end CnfForm

/-! Resolution. -/

variable [DecidableEq ν]

/-- Given `C = C' ∨ l` and `D = D' ∨ -l`, return `C' ∨ D'` with properties as in
`resolve_characterization`. -/
def resolve (C D : Clause ν) (l : Lit ν) : Clause ν :=
  (C.filter (· ≠ l) ++ D.filter (· ≠ -l))

theorem resolve_characterization (C D : Clause ν) (l : Lit ν) :
    ∃ (C' D' : Clause ν),
    (resolve C D l).toPropTerm = C'.toPropTerm ⊔ D'.toPropTerm ∧ 
    C' ⊆ C ∧ l ∉ C' ∧
    D' ⊆ D ∧ -l ∉ D' := by
  use C.filter (· ≠ l), D.filter (· ≠ -l)
  refine ⟨?eq, ?subC, ?memC, ?subD, ?memD⟩ <;>
    simp [resolve, Clause.toPropTerm_append, List.mem_filter]

/-- The clause C is Resolution IMPlied on a literal l w.r.t. a formula F when for every D ∈ F
containing -l, F implies the resolvent of C and D. Note that RAT implies RIMP by soundness of unit
propagation/AT. -/
-- TODO: there is potentially some subtlety here, in 'Inprocessing Rules' *each* resolvent of C with
-- D has to be implied.
def isRIMP (F : CnfForm ν) (C : Clause ν) (l : Lit ν) : Prop :=
  ∀ D ∈ F, -l ∈ D → F.toPropTerm ≤ (resolve C D l).toPropTerm

open PropTerm in
/-- Adding a RIMP clause on `l` preserves equisatisfiability over any set not containing `l`. -/
theorem equivalentOver_of_isRIMP [DecidableEq ν] {X : Set ν} (F : CnfForm ν) (C : Clause ν)
    (l : Lit ν) : l ∈ C → l.var ∉ X → isRIMP F C l →
    equivalentOver X F.toPropTerm (F.toPropTerm ⊓ C.toPropTerm) := by
  intro hLC hLX hRIMP τ
  refine ⟨fun ⟨σ, hσ, hF⟩ => ?ltr, by aesop⟩
  by_cases hσC : σ ⊨ C.toPropTerm
  . exact ⟨σ, hσ, by simp [hσC, hF]⟩
  . use σ.set l.var l.polarity
    constructor
    . exact σ.agreeOn_set l.polarity hLX |>.trans hσ
    . rw [satisfies_conj]
      constructor
      . rw [F.satisfies_iff]
        intro D hDF
        by_cases hLD : -l ∈ D
        . have ⟨C', D', hCD, hC'C, _, hD'D, hLD'⟩ := resolve_characterization C D l
          have hFCD := hCD ▸ hRIMP D hDF hLD
          have : σ ⊨ C'.toPropTerm ⊔ D'.toPropTerm := entails_ext.mp hFCD _ hF
          have : σ ⊭ C'.toPropTerm :=
            fun h => hσC <| entails_ext.mp (Clause.toPropTerm_monotone hC'C) _ h
          have : σ ⊨ D'.toPropTerm := by aesop
          have : σ.set l.var l.polarity ⊨ D'.toPropTerm :=
            D'.satisfies_of_neg_not_in σ l hLD' this
          exact entails_ext.mp (Clause.toPropTerm_monotone hD'D) _ this
        . exact D.satisfies_of_neg_not_in σ l hLD ((F.satisfies_iff).mp hF D hDF)
      . exact C.satisfies_set σ l hLC

-- PROBLEM: I think this is actually false. For example `x ∨ y` is RAT on `y` w.r.t `x` but `x`
-- does not extend uniquely to `x ∧ (x ∨ y)`.
open PropTerm in
theorem hasUniqueExtension_of_isRIMP {X : Set ν} (F : CnfForm ν) (C : Clause ν) (l : Lit ν) :
    l ∈ C → l.var ∉ X → isRIMP F C l →
    hasUniqueExtension X (X.insert l.var) (F.toPropTerm ⊓ C.toPropTerm) := by
  intro hC hX hRIMP σ₁ σ₂ h₁ h₂ hAgree
  sorry