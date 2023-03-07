import ProofChecker.Model.PropVars
import ProofChecker.Data.ICnf
import ProofChecker.CountModels

/-! Reasoning about definitional extensions. -/

namespace PropTerm

variable [DecidableEq ν]

theorem equivalentOver_def_ext {x : ν} {X : Set ν} (φ ψ : PropTerm ν) :
    ↑φ.semVars ⊆ X → ↑ψ.semVars ⊆ X → x ∉ X → equivalentOver X φ (φ ⊓ .biImpl (.var x) ψ) := by
  intro hφ hψ hMem τ
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    let σ₂ := σ₁.set x (ψ.eval σ₁)
    have hAgree₂₁ : σ₂.agreeOn X σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
    have : σ₂.agreeOn X τ := hAgree₂₁.trans hAgree
    have : σ₂ ⊨ φ := agreeOn_semVars (hAgree₂₁.subset hφ) |>.mpr h₁
    have : σ₂ ⊨ ψ ↔ σ₁ ⊨ ψ := agreeOn_semVars (hAgree₂₁.subset hψ)
    have : σ₂ ⊨ .biImpl (.var x) ψ := by aesop
    exact ⟨σ₂, by assumption, satisfies_conj.mpr (by constructor <;> assumption)⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    exact ⟨σ₂, hAgree, (satisfies_conj.mp h₂).left⟩

theorem equivalentOver_def_self {x : ν} {X : Set ν} (φ : PropTerm ν) :
    x ∉ X → ↑φ.semVars ⊆ X → equivalentOver X (.var x ⊓ .biImpl (.var x) φ) φ := by
  intro hMem hφ τ
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    simp only [satisfies_conj, satisfies_biImpl] at h₁
    exact ⟨σ₁, hAgree, h₁.right.mp h₁.left⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    let σ₁ := σ₂.set x ⊤
    have hAgree₁₂ : σ₁.agreeOn X σ₂ := σ₂.agreeOn_set_of_not_mem _ hMem
    have : σ₁.agreeOn X τ := hAgree₁₂.trans hAgree
    have : σ₁ ⊨ φ := agreeOn_semVars (hAgree₁₂.subset hφ) |>.mpr h₂
    exact ⟨σ₁, by assumption, satisfies_conj.mpr (by simp (config := {zeta := false}) [this])⟩

theorem disj_def_eq (x : ν) (φ₁ φ₂ : PropTerm ν) :
    ((.var x)ᶜ ⊔ φ₁ ⊔ φ₂) ⊓ (.var x ⊔ φ₁ᶜ) ⊓ (.var x ⊔ φ₂ᶜ) = .biImpl (.var x) (φ₁ ⊔ φ₂) := by
  ext τ
  cases h : τ x <;> simp [not_or, h]

theorem equivalentOver_disj_def_ext {x : ν} {X : Set ν} (φ φ₁ φ₂ : PropTerm ν) :
    ↑φ.semVars ⊆ X → ↑φ₁.semVars ⊆ X → ↑φ₂.semVars ⊆ X → x ∉ X →
    equivalentOver X φ (φ ⊓ ((.var x)ᶜ ⊔ φ₁ ⊔ φ₂) ⊓ (.var x ⊔ φ₁ᶜ) ⊓ (.var x ⊔ φ₂ᶜ)) := by
  intro hφ h₁ h₂ hMem
  rw [inf_assoc, inf_assoc, ← inf_assoc (a := (.var x)ᶜ ⊔ φ₁ ⊔ φ₂), disj_def_eq x φ₁ φ₂]
  have := Finset.coe_subset.mpr (semVars_disj φ₁ φ₂)
  apply equivalentOver_def_ext _ _ hφ (subset_trans this (by simp [*])) hMem
  
-- TODO: bigConj_def_eq

-- LATER: If needed, prove that disj_def also has UEP.

end PropTerm