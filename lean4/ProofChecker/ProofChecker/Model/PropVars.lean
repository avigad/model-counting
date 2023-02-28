/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.ByContra

import ProofChecker.Model.PropTerm

/-! Definitions and theorems relating propositional formulas and functions to variables

## Main definitions

`PropForm.vars` - the set of syntactic variables of a formula
`PropTerm.semVars` - the set of semantic variables of a function
`PropTerm.equivalentOver X` - two functions are equivalent over a set `X` of variables
`PropTerm.hasUniqueExtension X Y` - the assignments to a function extend uniquely from a set `X` to
a set `Y` of variables

NOTE: Semantic notions are not generally defined on `PropForm`s. They are expected to be used on
`PropForm`s by composing with `⟦-⟧`.

NOTE: We try to delay talking about dependently-typed functions `{x // x ∈ X} → Bool` for as long as
possible by developing the theory in terms of total assignments `ν → Bool`. Assignments with finite
domain are eventually considered in `ModelCount.lean`. -/

namespace PropAssignment

-- TODO: is this defined in mathlib for functions in general?
def agreeOn (X : Set ν) (σ₁ σ₂ : PropAssignment ν) : Prop :=
  ∀ x ∈ X, σ₁ x = σ₂ x

theorem agreeOn_refl (σ : PropAssignment ν) : agreeOn X σ σ :=
  fun _ _ => rfl
theorem agreeOn.symm : agreeOn X σ₁ σ₂ → agreeOn X σ₂ σ₁ :=
  fun h x hX => Eq.symm (h x hX)
theorem agreeOn.trans : agreeOn X σ₁ σ₂ → agreeOn X σ₂ σ₃ → agreeOn X σ₁ σ₃ :=
  fun h₁ h₂ x hX => Eq.trans (h₁ x hX) (h₂ x hX)

theorem agreeOn.subset : X ⊆ Y → agreeOn Y σ₁ σ₂ → agreeOn X σ₁ σ₂ :=
  fun hSub h x hX => h x (hSub hX)

theorem agreeOn_set {x : ν} {X : Set ν} [DecidableEq ν] (σ : PropAssignment ν) (v : Bool) : x ∉ X →
    agreeOn X (σ.set x v) σ := by
  -- I ❤ A️esop
  aesop (add norm unfold agreeOn, norm unfold set)

end PropAssignment

namespace PropForm

variable [DecidableEq ν]

/-- Variables appearing in the formula. Sometimes called its "support set". -/
def vars : PropForm ν → Finset ν
  | var y => {y}
  | tr | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

theorem eval_of_agreeOn_vars {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} : σ₁.agreeOn φ.vars σ₂ →
    φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  induction φ <;> simp_all [PropAssignment.agreeOn, eval, vars]

theorem eval_set_of_not_mem_vars {x : ν} {φ : PropForm ν} {τ : PropAssignment ν} : 
    x ∉ φ.vars → φ.eval (τ.set x b) = φ.eval τ := by
  intro hNMem
  apply eval_of_agreeOn_vars
  intro y hY
  have : y ≠ x := fun h => hNMem (h ▸ hY)
  simp [PropAssignment.set, this]

theorem agreeOn_vars {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.vars σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  intro h
  simp [SemanticEntails.entails, satisfies, eval_of_agreeOn_vars h]

set_option push_neg.use_distrib true in
lemma semVar_inversion (φ : PropForm ν) (τ : PropAssignment ν) (x : ν) : τ ⊨ φ →
    τ.set x (!τ x) ⊭ φ → x ∈ φ.vars := by
  intro hτ hτ'
  induction φ generalizing τ with
  | tr => exfalso; exact hτ' satisfies_tr
  | fls => exfalso; exact not_satisfies_fls hτ
  | var y =>
    simp_all only [vars, satisfies_var, Finset.mem_singleton]
    by_contra h
    exact hτ' (hτ ▸ τ.set_get_of_ne (!τ x) h)
  | _ =>
    simp_all only
      [satisfies_conj, satisfies_disj, satisfies_impl', satisfies_biImpl', vars, Finset.mem_union]
    push_neg at hτ'
    aesop
    
end PropForm
    
namespace PropTerm

variable [DecidableEq ν]

/-- See `semVars`. -/
private def semVars' (φ : PropTerm ν) : Set ν :=
  { x | ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ }

private theorem semVars'_subset_vars (φ : PropForm ν) : semVars' ⟦φ⟧ ⊆ φ.vars :=
  fun x ⟨τ, hτ, hτ'⟩ => PropForm.semVar_inversion φ τ x hτ hτ'
  
private instance semVars'_finite (φ : PropTerm ν) : Set.Finite φ.semVars' :=
  have ⟨φ', h⟩ := Quotient.exists_rep φ 
  Set.Finite.subset (Finset.finite_toSet _) (h ▸ semVars'_subset_vars φ')
  
/-- The *semantic variables* of `φ` are those it is sensitive to as a Boolean function.
Unlike `vars`, this set is stable under equivalence of formulas. -/
noncomputable def semVars (φ : PropTerm ν) : Finset ν :=
  Set.Finite.toFinset φ.semVars'_finite

theorem eval_of_agreeOn_semVars {φ : PropTerm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.semVars σ₂ → φ.eval σ₁ = φ.eval σ₂ := by
  -- LATER: This proof is tricky and I'm not sure we need it for the invariants.
  sorry

theorem agreeOn_semVars {φ : PropTerm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.semVars σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  intro h
  simp [SemanticEntails.entails, satisfies, eval_of_agreeOn_semVars h]

/-- Two functions φ₁ and φ₂ are equivalent over X when for every assignment τ, models of φ₁ 
extending τ over X are in bijection with models of φ₂ extending τ over X. -/
-- This is `sequiv` here: https://github.com/ccodel/verified-encodings/blob/master/src/cnf/encoding.lean
def equivalentOver (X : Set ν) (φ₁ φ₂ : PropTerm ν) :=
  ∀ τ, (∃ (σ₁ : PropAssignment ν), σ₁.agreeOn X τ ∧ σ₁ ⊨ φ₁) ↔
       (∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X τ ∧ σ₂ ⊨ φ₂)

theorem equivalentOver_refl (φ : PropTerm ν) : equivalentOver X φ φ :=
  fun _ => ⟨id, id⟩
theorem equivalentOver.symm : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₁ :=
  fun e τ => (e τ).symm
theorem equivalentOver.trans : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₃ →
    equivalentOver X φ₁ φ₃ :=
  fun e₁ e₂ τ => (e₁ τ).trans (e₂ τ)

theorem equivalentOver.subset {X Y : Set ν} : X ⊆ Y → equivalentOver Y φ₁ φ₂ →
    equivalentOver X φ₁ φ₂ := by
  intro hSub
  suffices ∀ φ₁ φ₂ τ, equivalentOver Y φ₁ φ₂ →
      (∃ (σ₁ : PropAssignment ν), σ₁.agreeOn X τ ∧ σ₁ ⊨ φ₁) →
      ∃ (σ₂ : PropAssignment ν), σ₂.agreeOn X τ ∧ σ₂ ⊨ φ₂ from
    fun e τ => ⟨this φ₁ φ₂ τ e, this φ₂ φ₁ τ e.symm⟩
  intro φ₁ φ₂ τ e ⟨σ₁, hA, hS⟩
  have ⟨σ₃, hA', hS'⟩ := (e σ₁).mp ⟨σ₁, σ₁.agreeOn_refl, hS⟩
  exact ⟨σ₃, hA'.subset hSub |>.trans hA, hS'⟩

theorem equivalentOver_semVars {X : Set ν} : φ₁.semVars ⊆ X → φ₂.semVars ⊆ X →
    equivalentOver X φ₁ φ₂ → φ₁ = φ₂ := by
  suffices ∀ {φ₁ φ₂} {τ : PropAssignment ν}, φ₂.semVars ⊆ X →
      equivalentOver X φ₁ φ₂ → τ ⊨ φ₁ → τ ⊨ φ₂ by
    intro h₁ h₂ e
    ext τ
    exact ⟨this h₂ e, this h₁ e.symm⟩
  intro φ₁ φ₂ τ h₂ e h
  have ⟨σ₁, hA, hS⟩ := (e τ).mp ⟨τ, τ.agreeOn_refl, h⟩
  have : σ₁ ⊨ φ₂ ↔ τ ⊨ φ₂ := agreeOn_semVars (hA.subset h₂)
  exact this.mp hS

-- TODO Now extensions. A definitional extension by a variable not in semVars
-- preserves s-equivalence
-- has unique extension
-- But what *is* a definitional extension?
-- x ∉ φ.semVars
-- maybe needed: x ∉ X0 (why? because X0 ⊆ semVars? well, that's false.)
-- φ ↦ φ ⊓ (-x ∨ l₁ ∨ l₂) ⊓ (x ∨ -l₁) ⊓ (x ∨ -l₂)

/-- A function has the unique extension property from `X` to `Y` (both sets of variables) when any
satisfying assignment, if it exists, is uniquely determined on `Y` by its values on `X`. Formally,
any two satisfying assignments which agree on `X` must also agree on `Y`. -/
/- TODO: Model equivalence is expected to follow from this. For example: 
equivalentOver φ₁.vars ⟦φ₁⟧ ⟦φ₂⟧ ∧ hasUniqueExtension ⟦φ₂⟧ φ₁.vars φ₂.vars →
{ σ : { x // x ∈ φ₁.vars} → Bool | σ ⊨ φ₁ } ≃ { σ : { x // x ∈ φ₂.vars } → Bool | σ ⊨ φ₂ } -/
def hasUniqueExtension (X Y : Set ν) (φ : PropTerm ν) :=
  ∀ (σ₁ σ₂ : PropAssignment ν), σ₁ ⊨ φ → σ₂ ⊨ φ → σ₁.agreeOn X σ₂ → σ₁.agreeOn Y σ₂

end PropTerm

namespace PropForm

variable [DecidableEq ν]

theorem equivalentOver_of_equivalent : equivalent φ₁ φ₂ → PropTerm.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ :=
  fun h => Quotient.sound h ▸ PropTerm.equivalentOver_refl ⟦φ₁⟧

theorem semVars_eq_of_equivalent (φ₁ φ₂ : PropForm ν) : equivalent φ₁ φ₂ →
    PropTerm.semVars ⟦φ₁⟧ = PropTerm.semVars ⟦φ₂⟧ := 
  fun h => Quotient.sound h ▸ rfl

theorem semVars_subset_vars (φ : PropForm ν) : PropTerm.semVars ⟦φ⟧ ⊆ φ.vars := by
  simp only [PropTerm.semVars, Set.Finite.toFinset_subset]
  exact PropTerm.semVars'_subset_vars φ

theorem equivalentOver_vars {X : Set ν} : φ₁.vars ⊆ X → φ₂.vars ⊆ X →
    PropTerm.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ → equivalent φ₁ φ₂ :=
  fun h₁ h₂ h => Quotient.exact
    (PropTerm.equivalentOver_semVars
      (subset_trans (semVars_subset_vars φ₁) h₁)
      (subset_trans (semVars_subset_vars φ₂) h₂)
      h)

end PropForm