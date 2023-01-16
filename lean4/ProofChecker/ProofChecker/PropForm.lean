/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra

import ProofChecker.ToMathlib

/-- A propositional formula over variables of type `ν`. -/
inductive PropForm (ν : Type u)
  | var (x : ν)
  | tr
  | fls
  | neg (φ : PropForm ν)
  | conj (φ₁ φ₂ : PropForm ν)
  | disj (φ₁ φ₂ : PropForm ν)
  | impl (φ₁ φ₂ : PropForm ν)
  | biImpl (φ₁ φ₂ : PropForm ν)
  deriving Repr, DecidableEq, Inhabited

namespace PropForm

-- HACK: a `let` doesn't work with structural recursion
local macro "go " n:ident : term =>
  `(let s := $(Lean.mkIdent `PropForm.toString) $n
    if s.contains ' ' then s!"({s})" else s)
protected def toString [ToString ν] : PropForm ν → String
  | var x        => toString x
  | tr           => "⊤"
  | fls          => "⊥"
  | neg φ        => s!"¬{go φ}"
  | conj φ₁ φ₂   => s!"{go φ₁} ∧ {go φ₂}"
  | disj φ₁ φ₂   => s!"{go φ₁} ∨ {go φ₂}"
  | impl φ₁ φ₂   => s!"{go φ₁} → {go φ₂}"
  | biImpl φ₁ φ₂ => s!"{go φ₁} ↔ {go φ₂}"

instance [ToString ν] : ToString (PropForm ν) :=
  ⟨PropForm.toString⟩

set_option trace.simps.debug true in
/-- Variables appearing in the formula. Sometimes called its "support set". -/
-- TODO: a finset or list variant may be useful; but ν can be a Fintype in which case Set ν works
@[simp]
def vars : PropForm ν → Set ν
  | var y => {y}
  | tr | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

end PropForm

/-- An assignment to propositional variables valued in `α`. -/
def PropAssignment (ν : Type u) (α : Type v) := ν → α

def PropAssignment.set [DecidableEq ν] (τ : PropAssignment ν α) (x : ν) (v : α) :
    PropAssignment ν α :=
  fun y => if y = x then v else τ y

/-! Any propositional assignment valued in a Boolean algebra extends uniquely to an evaluation
function on formulas. -/

namespace PropForm

variable [BooleanAlgebra α]

@[simp]
def eval (τ : PropAssignment ν α) : PropForm ν → α
  | var x => τ x
  | tr => ⊤
  | fls => ⊥
  | neg φ => (eval τ φ)ᶜ
  | conj φ₁ φ₂ => (eval τ φ₁) ⊓ (eval τ φ₂)
  | disj φ₁ φ₂ => (eval τ φ₁) ⊔ (eval τ φ₂)
  | impl φ₁ φ₂ => (eval τ φ₁) ⇨ (eval τ φ₂)
  | biImpl φ₁ φ₂ => (eval τ φ₁ ⇨ eval τ φ₂) ⊓ (eval τ φ₂ ⇨ eval τ φ₁)

theorem eval_ext {φ : PropForm ν} {σ₁ σ₂ : PropAssignment ν α} : (∀ x ∈ φ.vars, σ₁ x = σ₂ x) →
    φ.eval σ₁ = φ.eval σ₂ := by
  intro h
  induction φ with
  | var y => apply h; simp 
  | tr | fls => rfl
  | neg _ ih => simp [ih h]
  | _ _ _ ih₁ ih₂ =>
    simp [ih₁ fun x hMem => (h x <| .inl hMem), ih₂ fun x hMem => (h x <| .inr hMem)]

theorem eval_set_of_not_mem_vars [DecidableEq ν] {x : ν} {φ : PropForm ν} {τ : PropAssignment ν α} : 
    x ∉ φ.vars → φ.eval (τ.set x b) = φ.eval τ := by
  intro hNMem
  apply eval_ext
  intro y hY
  have : y ≠ x := fun h => hNMem (h ▸ hY)
  simp [PropAssignment.set, this]

/-- We say a formula `φ₁` semantically entails `φ₂` when it does so in every Boolean-valued model.

This basically postulates monotonicity of homs out of the term model `PropTerm` by fiat. We could
do better by showing soundness and completness of some proof system or of two-valued models. See
https://awodey.github.io/catlog/notes/catlog2.pdf . -/
def entails (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ ⦃α : Type⦄ [BooleanAlgebra α] (τ : PropAssignment ν α), φ₁.eval τ ≤ φ₂.eval τ

theorem entails_refl : entails φ φ :=
  fun _ _ _ => le_rfl
theorem entails.trans : entails φ ψ → entails ψ θ → entails φ θ :=
  fun h₁ h₂ _ _ τ => le_trans (h₁ τ) (h₂ τ)

theorem entails_tr (φ : PropForm ν) : entails φ tr :=
  fun _ _ _ => le_top
theorem fls_entails (φ : PropForm ν) : entails fls φ :=
  fun _ _ _ => bot_le

theorem entails_disj_left (φ ψ : PropForm ν) : entails φ (disj φ ψ) :=
  fun _ _ _ => le_sup_left
theorem entails_disj_right (φ ψ : PropForm ν) : entails ψ (disj φ ψ) :=
  fun _ _ _ => le_sup_right
theorem disj_entails : entails φ θ → entails ψ θ → entails (disj φ ψ) θ :=
  fun h₁ h₂ _ _ τ => sup_le (h₁ τ) (h₂ τ)

theorem conj_entails_left (φ ψ : PropForm ν) : entails (conj φ ψ) φ :=
  fun _ _ _ => inf_le_left
theorem conj_entails_right (φ ψ : PropForm ν) : entails (conj φ ψ) ψ :=
  fun _ _ _ => inf_le_right
theorem entails_conj : entails φ ψ → entails φ θ → entails φ (conj ψ θ) :=
  fun h₁ h₂ _ _ τ => le_inf (h₁ τ) (h₂ τ)

theorem entails_impl_iff (φ ψ θ : PropForm ν) : entails φ (impl ψ θ) ↔ entails (conj φ ψ) θ :=
  ⟨fun h _ _ τ => le_himp_iff.mp (h τ), fun h _ _ τ => le_himp_iff.mpr (h τ)⟩

theorem entails_disj_conj (φ ψ θ : PropForm ν) :
    entails (conj (disj φ ψ) (disj φ θ)) (disj φ (conj ψ θ)) :=
  fun _ _ _ => le_sup_inf

theorem conj_neg_entails_fls (φ : PropForm ν) : entails (conj φ (neg φ)) fls :=
  fun _ _ τ => BooleanAlgebra.inf_compl_le_bot (eval τ φ)

theorem tr_entails_disj_neg (φ : PropForm ν) : entails tr (disj φ (neg φ)) :=
  fun _ _ τ => BooleanAlgebra.top_le_sup_compl (eval τ φ)

/-- Two formulas are semantically equivalent when they evaluate to the same thing in every
Boolean-valued model. -/
def equivalent (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ ⦃α : Type⦄ [BooleanAlgebra α] (τ : PropAssignment ν α), φ₁.eval τ = φ₂.eval τ

theorem equivalent_refl (φ : PropForm ν) : equivalent φ φ :=
  fun _ _ _ => rfl
theorem equivalent.symm : equivalent φ ψ → equivalent ψ φ :=
  fun h _ _ τ => (h τ).symm
theorem equivalent.trans : equivalent φ ψ → equivalent ψ θ → equivalent φ θ :=
  fun h₁ h₂ _ _ τ => (h₁ τ).trans (h₂ τ) 

theorem entails.antisymm : entails φ ψ → entails ψ φ → equivalent φ ψ :=
  fun h₁ h₂ _ _ τ => le_antisymm (h₁ τ) (h₂ τ)

theorem impl_fls (φ : PropForm ν) : equivalent (impl φ fls) (neg φ) :=
  fun _ _ τ => himp_bot (eval τ φ)

end PropForm