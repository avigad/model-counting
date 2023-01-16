/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import ProofChecker.PropForm

/-! The term model of propositional formulas. We show that it is a Heyting algebra. -/

open PropForm in
instance PropTerm.setoid (ν : Type) : Setoid (PropForm ν) where
  r := equivalent
  iseqv := {
    refl  := equivalent_refl
    symm  := equivalent.symm
    trans := equivalent.trans
  }

/-- A propositional term is a propositional formula up to semantic equivalence. -/
def PropTerm ν := Quotient (PropTerm.setoid ν)

namespace PropTerm

def var (x : ν) : PropTerm ν := ⟦.var x⟧

def tr : PropTerm ν := ⟦.tr⟧

def fls : PropTerm ν := ⟦.fls⟧

def neg : PropTerm ν → PropTerm ν :=
  Quotient.map (.neg ·) (by
    intro _ _ h _ _ τ
    simp [h τ])

def conj : PropTerm ν → PropTerm ν → PropTerm ν := 
  Quotient.map₂ (.conj · ·) (by
    intro _ _ h₁ _ _ h₂ _ _ τ
    simp [h₁ τ, h₂ τ])

def disj : PropTerm ν → PropTerm ν → PropTerm ν :=
  Quotient.map₂ (.disj · ·) (by
    intro _ _ h₁ _ _ h₂ _ _ τ
    simp [h₁ τ, h₂ τ])

def impl : PropTerm ν → PropTerm ν → PropTerm ν :=
  Quotient.map₂ (.impl · ·) (by
    intro _ _ h₁ _ _ h₂ _ _ τ
    simp [h₁ τ, h₂ τ])

def biImpl : PropTerm ν → PropTerm ν → PropTerm ν :=
  Quotient.map₂ (.biImpl · ·) (by
    intro _ _ h₁ _ _ h₂ _ _ τ
    simp [h₁ τ, h₂ τ])

def entails : PropTerm ν → PropTerm ν → Prop :=
  Quotient.lift₂ (PropForm.entails · ·) (by
    intro _ _ _ _ h₁ h₂
    dsimp [HasEquiv.Equiv, Setoid.r, PropForm.equivalent] at h₁ h₂
    simp [PropForm.entails, h₁, h₂])

-- TODO: All of these just lift the corresponding lemmas from PropFrom, is there a quicker way?

theorem entails_refl (φ : PropTerm ν) : entails φ φ := by
  have ⟨φ, h⟩ := Quotient.exists_rep φ
  simp [← h, entails, PropForm.entails]

theorem entails.trans : entails φ ψ → entails ψ θ → entails φ θ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  have ⟨θ, h₃⟩ := Quotient.exists_rep θ
  simp only [← h₁, ← h₂, ← h₃]
  exact PropForm.entails.trans

theorem entails.antisymm : entails φ ψ → entails ψ φ → φ = ψ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  simp only [← h₁, ← h₂, entails, Quotient.lift₂_mk]
  rw [Quotient.eq]
  exact PropForm.entails.antisymm

theorem entails_tr (φ : PropTerm ν) : entails φ tr := by
  have ⟨φ, h⟩ := Quotient.exists_rep φ
  simp [← h, entails, tr, PropForm.entails_tr]

theorem fls_entails (φ : PropTerm ν) : entails fls φ := by
  have ⟨φ, h⟩ := Quotient.exists_rep φ
  simp [← h, entails, fls, PropForm.fls_entails]

theorem entails_disj_left (φ ψ : PropTerm ν) : entails φ (disj φ ψ) := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  simp [← h₁, ← h₂, entails, disj, PropForm.entails_disj_left]

theorem entails_disj_right (φ ψ : PropTerm ν) : entails ψ (disj φ ψ) := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  simp [← h₁, ← h₂, entails, disj, PropForm.entails_disj_right]

theorem disj_entails : entails φ θ → entails ψ θ → entails (disj φ ψ) θ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  have ⟨θ, h₃⟩ := Quotient.exists_rep θ
  simp only [← h₁, ← h₂, ← h₃, entails, disj, Quotient.lift₂_mk, Quotient.map₂_mk]
  exact PropForm.disj_entails

theorem conj_entails_left (φ ψ : PropTerm ν) : entails (conj φ ψ) φ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  simp [← h₁, ← h₂, entails, conj, PropForm.conj_entails_left]

theorem conj_entails_right (φ ψ : PropTerm ν) : entails (conj φ ψ) ψ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  simp [← h₁, ← h₂, entails, conj, PropForm.conj_entails_right]

theorem entails_conj : entails φ ψ → entails φ θ → entails φ (conj ψ θ) := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  have ⟨θ, h₃⟩ := Quotient.exists_rep θ
  simp only [← h₁, ← h₂, ← h₃, entails, conj, Quotient.lift₂_mk, Quotient.map₂_mk]
  exact PropForm.entails_conj

theorem entails_impl_iff (φ ψ θ : PropTerm ν) : entails φ (impl ψ θ) ↔ entails (conj φ ψ) θ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  have ⟨θ, h₃⟩ := Quotient.exists_rep θ
  simp [← h₁, ← h₂, ← h₃, entails, impl, conj, PropForm.entails_impl_iff]

theorem impl_fls (φ : PropTerm ν) : impl φ fls = neg φ := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  simp only [← h₁, impl, fls, neg, Quotient.map_mk, Quotient.map₂_mk]
  rw [Quotient.eq]
  exact PropForm.impl_fls φ

theorem conj_neg_entails_fls (φ : PropTerm ν) : entails (conj φ (neg φ)) fls := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  simp [← h₁, entails, conj, neg, fls, PropForm.conj_neg_entails_fls]

theorem tr_entails_disj_neg (φ : PropTerm ν) : entails tr (disj φ (neg φ)) := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  simp [← h₁, entails, tr, disj, neg, PropForm.tr_entails_disj_neg]

theorem entails_disj_conj (φ ψ θ : PropTerm ν) :
    entails (conj (disj φ ψ) (disj φ θ)) (disj φ (conj ψ θ)) := by
  have ⟨φ, h₁⟩ := Quotient.exists_rep φ
  have ⟨ψ, h₂⟩ := Quotient.exists_rep ψ
  have ⟨θ, h₃⟩ := Quotient.exists_rep θ
  simp [← h₁, ← h₂, ← h₃, entails, conj, disj, PropForm.entails_disj_conj]

instance : BooleanAlgebra (PropTerm ν) where
  le := entails
  top := tr
  bot := fls
  compl := neg
  sup := disj
  inf := conj
  le_refl := entails_refl
  le_trans := @entails.trans _
  le_antisymm := @entails.antisymm _
  le_top := entails_tr
  bot_le := fls_entails
  le_sup_left := entails_disj_left
  le_sup_right := entails_disj_right
  sup_le _ _ _ := disj_entails
  inf_le_left := conj_entails_left
  inf_le_right := conj_entails_right
  le_inf _ _ _ := entails_conj
  le_sup_inf := entails_disj_conj
  inf_compl_le_bot := conj_neg_entails_fls
  top_le_sup_compl := tr_entails_disj_neg

end PropTerm
