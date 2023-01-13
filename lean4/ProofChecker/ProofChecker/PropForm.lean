/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.ByContra
import Aesop

import ProofChecker.ToMathlib

/-- A propositional formula over variables of type `ν`. -/
inductive PropForm (ν : Type)
  | var (x : ν)
  | tr
  | fls
  | neg (φ : PropForm ν)
  | conj (φ₁ φ₂ : PropForm ν)
  | disj (φ₁ φ₂ : PropForm ν)
  | impl (φ₁ φ₂ : PropForm ν)
  | biImpl (φ₁ φ₂ : PropForm ν)
  deriving Repr, DecidableEq, Inhabited

variable {ν : Type} [DecidableEq ν]

namespace PropForm

/-- Variables appearing in the formula. Sometimes called its "support set". -/
-- TODO: it could be a finset or list; unless we make ν a fintype
def vars (φ : PropForm ν) : Set ν :=
  fun x => match φ with
  | var y => x = y
  | tr | fls => false
  | neg φ => x ∈ vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => x ∈ vars φ₁ ∨ x ∈ vars φ₂

@[simp]
theorem vars_var { x : ν } : (var x).vars = {x} := rfl

@[simp]
theorem vars_tr : (tr : PropForm ν).vars = ∅ := by
  simp [vars, Membership.mem, Set.Mem, EmptyCollection.emptyCollection]
  
@[simp]
theorem vars_fls : (fls : PropForm ν).vars = ∅ := by
  simp [vars, Membership.mem, Set.Mem, EmptyCollection.emptyCollection]

@[simp]
theorem vars_neg : (neg φ).vars = φ.vars := rfl

@[simp]
theorem vars_conj : (conj φ₁ φ₂).vars = φ₁.vars ∪ φ₂.vars := rfl

@[simp]
theorem vars_disj : (disj φ₁ φ₂).vars = φ₁.vars ∪ φ₂.vars := rfl

@[simp]
theorem vars_impl : (impl φ₁ φ₂).vars = φ₁.vars ∪ φ₂.vars := rfl

@[simp]
theorem vars_biImpl : (biImpl φ₁ φ₂).vars = φ₁.vars ∪ φ₂.vars := rfl

end PropForm

/-- An assignment of truth values to all variables. -/
def PropAssignment (ν : Type) := ν → Bool

namespace PropAssignment

def set (τ : PropAssignment ν) (x : ν) (v : Bool) : PropAssignment ν :=
  fun y => if y = x then v else τ y

end PropAssignment

namespace PropForm

def eval (τ : PropAssignment ν) : PropForm ν → Bool
  | var x => τ x
  | tr => true
  | fls => false
  | neg φ => !(eval τ φ)
  | conj φ₁ φ₂ => (eval τ φ₁) && (eval τ φ₂)
  | disj φ₁ φ₂ => (eval τ φ₁) || (eval τ φ₂)
  | impl φ₁ φ₂ => !(eval τ φ₁) || (eval τ φ₂)
  | biImpl φ₁ φ₂ => eval τ φ₁ = eval τ φ₂

theorem eval_ext {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν} : (∀ x ∈ φ.vars, σ₁ x = σ₂ x) →
    φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  induction φ with
  | var y =>
    apply h
    simp [h]
  | tr | fls => rfl
  | neg _ ih =>
    simp only [vars_neg] at h
    simp [eval, ih h]
  | _ _ _ ih₁ ih₂ =>
    simp only [vars_conj, vars_disj, vars_impl, vars_biImpl, Set.mem_union] at h
    simp [eval, ih₁ fun x hMem => (h x <| .inl hMem), ih₂ fun x hMem => (h x <| .inr hMem)]

theorem eval_set_of_not_mem_vars {x : ν} {φ : PropForm ν} {τ : PropAssignment ν} : 
    x ∉ φ.vars → φ.eval (τ.set x b) = φ.eval τ := by
  intro hNMem
  apply eval_ext
  intro y hY
  have : y ≠ x := fun h => hNMem (h ▸ hY)
  simp [PropAssignment.set, this]

end PropForm

/-! Satisfying assignments, satisfiability, validity -/

/-- An assignment satisfies a formula φ when φ evaluates to `true` at that assignment. -/
def PropAssignment.satisfies (τ : PropAssignment ν) (φ : PropForm ν) : Prop :=
  φ.eval τ = true

instance {ν : Type} : SemanticEntails (PropAssignment ν) (PropForm ν) where
  entails := PropAssignment.satisfies

namespace PropForm
open SemanticEntails PropAssignment

theorem satisfies_var {τ : PropAssignment ν} {x : ν} : τ ⊨ var x ↔ τ x :=
  by simp [entails, satisfies, eval]

theorem satisfies_tr {τ : PropAssignment ν} : τ ⊨ tr :=
  by simp [entails, satisfies, eval]

theorem not_satisfies_fls {τ : PropAssignment ν} : τ ⊭ fls :=
  fun h => nomatch h

theorem satisfies_neg {τ : PropAssignment ν} {φ : PropForm ν} : τ ⊨ neg φ ↔ τ ⊭ φ :=
  by simp [entails, satisfies, eval]

theorem satisfies_conj {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ conj φ₁ φ₂ ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ :=
  by simp [entails, satisfies, eval]

theorem satisfies_disj {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .disj φ₁ φ₂ ↔ τ ⊨ φ₁ ∨ τ ⊨ φ₂ :=
  by simp [entails, satisfies, eval]

theorem satisfies_impl {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .impl φ₁ φ₂ ↔ τ ⊭ φ₁ ∨ τ ⊨ φ₂ :=
  by simp [entails, satisfies, eval]

theorem satisfies_impl' {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .impl φ₁ φ₂ ↔ (τ ⊨ φ₁ → τ ⊨ φ₂) := by
  dsimp [entails, satisfies, eval]
  cases (eval τ φ₁) <;> cases (eval τ φ₂) <;> simp

theorem satisfies_biImpl {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .biImpl φ₁ φ₂ ↔ (τ ⊨ φ₁ ↔ τ ⊨ φ₂) :=
  by simp [entails, satisfies, eval]

def satisfiable (φ : PropForm ν) : Prop :=
  ∃ τ : PropAssignment ν, τ ⊨ φ

def valid (φ : PropForm ν) : Prop :=
  ∀ τ : PropAssignment ν, τ ⊨ φ

end PropForm

/-! Equivalence of formulas -/

namespace PropForm

/-- A formula entails another when every satisfying assignment to one satisfies the other. -/
def entails (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ {τ : PropAssignment ν}, τ ⊨ φ₁ → τ ⊨ φ₂

instance : SemanticEntails (PropForm ν) (PropForm ν) where
  entails := entails

def equivalent (φ₁ φ₂ : PropForm ν) : Prop :=
  φ₁ ⊨ φ₂ ∧ φ₂ ⊨ φ₁

scoped infix:51 " ≡ " => equivalent

-- This is false because e.g. x ∨ ¬x ≡ ⊤ but it should be true after replacing vars with depVars,
-- those being x ∈ φ.depVars ↔ ∃ τ, τ ⊨ φ ∧ τ.set x (!τ x) ⊭ φ
-- theorem eq_vars_of_equivalent {φ₁ φ₂ : PropForm ν} : φ₁ ≡ φ₂ → φ₁.vars = φ₂.vars

end PropForm

open scoped PropForm

/-! Assignments to subsets of variables 

We try to delay talking about functions `{x // x ∈ X} → Bool` by developing the theory
in terms of assignments `ν → Bool` for as long as possible. Maybe we can avoid these altogether
by instantiating `ν` with a fintype. -/

def agreeOn (X : Set ν) (σ₁ σ₂ : PropAssignment ν) : Prop :=
  ∀ x ∈ X, σ₁ x = σ₂ x

theorem agreeOn.refl : agreeOn X σ σ :=
  fun _ _ => rfl

theorem agreeOn.contravariant : X ⊆ Y → agreeOn Y σ₁ σ₂ → agreeOn X σ₁ σ₂ :=
  fun hSub h x hX => h x (hSub hX)

theorem agreeOn_vars : agreeOn φ.vars σ₁ σ₂ → (σ₁ ⊨ φ ↔ σ₂ ⊨ φ) := by
  intro h
  have := PropForm.eval_ext h
  simp [SemanticEntails.entails, PropAssignment.satisfies, this]

/-- Models of φ extending τ over X are those which agree with τ over X. -/
def modelsExtendingOver (φ : PropForm ν) (τ : PropAssignment ν) (X : Set ν) : Set (PropAssignment ν) :=
  fun σ => agreeOn X σ τ ∧ σ ⊨ φ

theorem modelsExtendingOver.contravariant : X ⊆ Y → modelsExtendingOver φ τ Y ⊆ modelsExtendingOver φ τ X := by
  intro hSub
  dsimp [modelsExtendingOver]
  intro σ hσ
  exact ⟨agreeOn.contravariant hSub hσ.left, hσ.right⟩

/-- Two formulas φ₁ are equivalent over X when for every assignment τ, models of φ₁ extending τ
over X are in bijection with models of φ₂ extending τ over X. -/
def equivalentOver (X : Set ν) (φ₁ φ₂ : PropForm ν) :=
  ∀ τ, modelsExtendingOver φ₁ τ X ≃ modelsExtendingOver φ₂ τ X

theorem equivalentOver.refl : equivalentOver X φ₁ φ₁ :=
  fun _ => Equiv.ofBijective id Function.bijective_id

theorem equivalentOver.symm : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₁ :=
  fun e τ => (e τ).symm

theorem equivalentOver.trans : equivalentOver X φ₁ φ₂ → equivalentOver X φ₂ φ₃ → equivalentOver X φ₁ φ₃ :=
  fun e₁ e₂ τ => (e₁ τ).trans (e₂ τ)

theorem equivalentOver_of_equivalent : φ₁ ≡ φ₂ → equivalentOver X φ₁ φ₂ := by
  intro ⟨hL, hR⟩ τ
  apply Equiv.ofBijective (fun ⟨σ, hσ⟩ => ⟨σ, ⟨hσ.left, hL hσ.right⟩⟩)
  apply Function.bijective_iff_has_inverse.mpr
  use (fun ⟨σ, hσ⟩ => ⟨σ, ⟨hσ.left, hR hσ.right⟩⟩)
  apply And.intro <;> {
    apply Function.leftInverse_iff_comp.mpr
    rfl
  }

theorem equivalent_of_equivalentOver_vars : φ₁.vars = φ₂.vars → equivalentOver φ₁.vars φ₁ φ₂ → φ₁ ≡ φ₂ := by
  intro h e
  apply And.intro
  . intro τ hφ₁
    have ⟨a, ha⟩ := e τ ⟨τ, agreeOn.refl, hφ₁⟩
    rw [h] at ha
    exact agreeOn_vars ha.left |>.mp ha.right
  . intro τ hφ₂
    have ⟨a, ha⟩ := e τ |>.symm ⟨τ, agreeOn.refl, hφ₂⟩
    exact agreeOn_vars ha.left |>.mp ha.right

