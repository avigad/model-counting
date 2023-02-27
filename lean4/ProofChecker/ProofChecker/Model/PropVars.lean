/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.ByContra

import ProofChecker.Model.PropTerm

/-! Assignments to and equivalence over subsets of variables. This usefully does respect semantic
equivalence, even though the operation `PropForm.vars` we define later does not. 

NOTE: We try to delay talking about dependently-typed functions `{x // x ∈ X} → Bool` for as long as
possible by developing the theory in terms of total assignments `ν → Bool`. Maybe we can avoid these
altogether by instantiating `ν` with a fintype. Potentially we could also quotient by `agreeOn X`. -/

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

theorem agreeOn.antitone : X ⊆ Y → agreeOn Y σ₁ σ₂ → agreeOn X σ₁ σ₂ :=
  fun hSub h x hX => h x (hSub hX)

-- TODO: mathlib name for the fun x => x?
theorem agreeOn_iff : agreeOn X σ₁ σ₂ ↔ (σ₁ ∘ (fun x => x) = σ₂ ∘ (fun x => x)) :=
  sorry

theorem agreeOn_set {x : ν} {X : Set ν} [DecidableEq ν] (σ : PropAssignment ν) (v : Bool) : x ∉ X →
    agreeOn X (σ.set x v) σ := by
  -- I ❤ A️esop
  aesop (add norm unfold agreeOn, norm unfold set)

end PropAssignment

namespace PropTerm

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

/-- A function has the unique extension property from `X` to `Y` (both sets of variables) when any
satisfying assignment, if it exists, is uniquely determined on `Y` by its values on `X`. Formally,
any two satisfying assignments which agree on `X` must also agree on `Y`. -/
/- TODO: Model equivalence is expected to follow from this. For example: 
equivalentOver φ₁.vars ⟦φ₁⟧ ⟦φ₂⟧ ∧ hasUniqueExtension ⟦φ₂⟧ φ₁.vars φ₂.vars →
{ σ : { x // x ∈ φ₁.vars} → Bool | σ ⊨ φ₁ } ≃ { σ : { x // x ∈ φ₂.vars } → Bool | σ ⊨ φ₂ } -/
def hasUniqueExtension (X Y : Set ν) (φ : PropTerm ν) :=
  ∀ (σ₁ σ₂ : PropAssignment ν), σ₁ ⊨ φ → σ₂ ⊨ φ → σ₁.agreeOn X σ₂ → σ₁.agreeOn Y σ₂

end PropTerm

open Classical

namespace PropForm

variable [DecidableEq ν]

/-- Variables appearing in the formula. Sometimes called its "support set". -/
def vars : PropForm ν → Finset ν
  | var y => {y}
  | tr | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

theorem eval_ext {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} : (∀ x ∈ φ.vars, σ₁ x = σ₂ x) →
    φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  induction φ <;> simp_all [eval, vars]

theorem eval_set_of_not_mem_vars [DecidableEq ν] {x : ν} {φ : PropForm ν} {τ : PropAssignment ν} : 
    x ∉ φ.vars → φ.eval (τ.set x b) = φ.eval τ := by
  intro hNMem
  apply eval_ext
  intro y hY
  have : y ≠ x := fun h => hNMem (h ▸ hY)
  simp [PropAssignment.set, this]

theorem agreeOn_vars {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} :
    σ₁.agreeOn φ.vars σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  intro h
  simp [SemanticEntails.entails, satisfies, eval_ext h]

-- theorem equivalent_of_equivalentOver_vars : φ₁.vars = φ₂.vars →
--     PropTerm.equivalentOver φ₁.vars ⟦φ₁⟧ ⟦φ₂⟧ → equivalent φ₁ φ₂ := by
--   intro h e
--   apply equivalent_ext.mpr
--   intro τ
--   sorry

theorem equivalentOver_of_equivalent : equivalent φ₁ φ₂ → PropTerm.equivalentOver X ⟦φ₁⟧ ⟦φ₂⟧ :=
  fun h => Quotient.sound h ▸ PropTerm.equivalentOver_refl ⟦φ₁⟧

/-- See `semVars`. -/
def semVars' (φ : PropForm ν) : Set ν :=
  { x | ∃ (τ : PropAssignment ν), τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ }

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

theorem semVars'_subset_vars (φ : PropForm ν) : φ.semVars' ⊆ φ.vars :=
  fun x ⟨τ, hτ, hτ'⟩ => semVar_inversion φ τ x hτ hτ'
  
instance semVars'_finite (φ : PropForm ν) : Set.Finite φ.semVars' :=
  Set.Finite.subset (Finset.finite_toSet _) φ.semVars'_subset_vars
  
/-- The *semantic variables* of `φ` are those it is sensitive to as a Boolean function.
Unlike `vars`, this set is stable under equivalence of formulas. -/
noncomputable def semVars (φ : PropForm ν) : Finset ν :=
  Set.Finite.toFinset φ.semVars'_finite
  
theorem semVars_subset_vars (φ : PropForm ν) : φ.semVars ⊆ φ.vars := by
  simp only [semVars, Set.Finite.toFinset_subset]
  exact φ.semVars'_subset_vars
  
theorem semVars_eq_of_equivalent (φ₁ φ₂ : PropForm ν) : equivalent φ₁ φ₂ →
    φ₁.semVars = φ₂.semVars := by
  suffices ∀ (φ₁ φ₂ : PropForm ν), equivalent φ₁ φ₂ → φ₁.semVars ⊆ φ₂.semVars from
    fun hEquiv => Finset.ext fun _ =>
      ⟨fun h => this φ₁ φ₂ hEquiv h,
       fun h => this φ₂ φ₁ (equivalent.symm hEquiv) h⟩
  intro φ₁ φ₂ hEquiv x
  simp only [semVars, semVars', Set.Finite.mem_toFinset, Set.mem_setOf_eq, exists_imp, and_imp]
  intro τ hτ hτ'
  exact ⟨τ,
    equivalent_ext.mp hEquiv _ |>.mp hτ,
    fun h => hτ' (equivalent_ext.mp hEquiv _ |>.mpr h)⟩

end PropForm

namespace PropTerm

/-- See `PropForm.semVars`. -/
noncomputable def semVars : PropTerm ν → Finset ν :=
  Quotient.lift PropForm.semVars PropForm.semVars_eq_of_equivalent
  
-- Now extensions. A definitional extension by a variable not in semVars
-- preserves s-equivalence
-- has unique extension
-- But what *is* a definitional extension?
-- x ∉ φ.semVars
-- maybe needed: x ∉ X0 (why? because X0 ⊆ semVars? well, that's false.)
-- φ ↦ φ ⊓ (-x ∨ l₁ ∨ l₂) ⊓ (x ∨ -l₁) ⊓ (x ∨ -l₂)

end PropTerm