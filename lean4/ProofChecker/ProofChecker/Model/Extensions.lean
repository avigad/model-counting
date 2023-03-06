import ProofChecker.Model.PropVars
import ProofChecker.Data.ICnf

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

theorem induction_step_sum (Γ l₁ l₂ φ₁ φ₂ : PropTerm Var) :
    s ∉ X → ↑Γ.semVars ⊆ X → ↑l₁.semVars ⊆ X → ↑l₂.semVars ⊆ X →
    equivalentOver X (l₁ ⊓ Γ) φ₁ → equivalentOver X (l₂ ⊓ Γ) φ₂ →
    equivalentOver X (.var s ⊓ Γ ⊓ (.biImpl (.var s) (l₁ ⊔ l₂))) (φ₁ ⊔ φ₂) := by
  intro hMem hΓ hL₁ hL₂ e₁ e₂ τ
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    have : σ₁ ⊨ l₁ ⊔ l₂ := by aesop
    cases satisfies_disj.mp this with
    | inl h =>
      have : σ₁ ⊨ l₁ ⊓ Γ := by simp_all
      have ⟨σ₂, hAgree₂, h₂⟩ := e₁ τ |>.mp ⟨σ₁, hAgree, this⟩
      exact ⟨σ₂, hAgree₂, satisfies_disj.mpr (.inl h₂)⟩
    | inr h =>
      have : σ₁ ⊨ l₂ ⊓ Γ := by simp_all
      have ⟨σ₂, hAgree₂, h₂⟩ := e₂ τ |>.mp ⟨σ₁, hAgree, this⟩
      exact ⟨σ₂, hAgree₂, satisfies_disj.mpr (.inr h₂)⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    have : σ₂ ⊨ φ₁ ⊔ φ₂ := by simp_all
    cases satisfies_disj.mp this with
    | inl h =>
      have ⟨σ₁, hAgree₁, h₁⟩ := e₁ τ |>.mpr ⟨σ₂, hAgree, h⟩
      let σ₁' := σ₁.set s ⊤
      have : σ₁' ⊨ .var s := by simp
      have hAgree₁' : σ₁'.agreeOn X σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
      have : σ₁'.agreeOn X τ := hAgree₁'.trans hAgree₁
      have : σ₁' ⊨ Γ := agreeOn_semVars (hAgree₁'.subset hΓ) |>.mpr (satisfies_conj.mp h₁).right
      have : σ₁' ⊨ l₁ := agreeOn_semVars (hAgree₁'.subset hL₁) |>.mpr (satisfies_conj.mp h₁).left
      exact ⟨σ₁', by assumption, by simp_all⟩
    | inr h =>
      have ⟨σ₁, hAgree₁, h₁⟩ := e₂ τ |>.mpr ⟨σ₂, hAgree, h⟩
      let σ₁' := σ₁.set s ⊤
      have : σ₁' ⊨ .var s := by simp
      have hAgree₁' : σ₁'.agreeOn X σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
      have : σ₁'.agreeOn X τ := hAgree₁'.trans hAgree₁
      have : σ₁' ⊨ Γ := agreeOn_semVars (hAgree₁'.subset hΓ) |>.mpr (satisfies_conj.mp h₁).right
      have : σ₁' ⊨ l₂ := agreeOn_semVars (hAgree₁'.subset hL₂) |>.mpr (satisfies_conj.mp h₁).left
      exact ⟨σ₁', by assumption, by simp_all⟩

-- Alternative: use disjoint variables condition on φ₁/φ₂ to put together pair of assignments?!
theorem induction_step_prod₂ (Γ l₁ l₂ φ₁ φ₂ : PropTerm Var) :
    s ∉ X → ↑Γ.semVars ⊆ X → ↑l₁.semVars ⊆ X → ↑l₂.semVars ⊆ X → ↑φ₁.semVars ⊆ X → ↑φ₂.semVars ⊆ X →
    equivalentOver X (l₁ ⊓ Γ) φ₁ → equivalentOver X (l₂ ⊓ Γ) φ₂ →
    equivalentOver X (.var s ⊓ (.biImpl (.var s) (l₁ ⊓ l₂)) ⊓ Γ) (φ₁ ⊓ φ₂) := by
  intro hMem hΓ hL₁ hL₂ hφ₁ hφ₂ e₁ e₂ τ
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    have : σ₁ ⊨ l₁ ⊓ Γ := by aesop
    have ⟨_, hAgree₂, h₂⟩ := e₁ τ |>.mp ⟨σ₁, hAgree, this⟩
    have : τ ⊨ φ₁ := agreeOn_semVars (hAgree₂.subset hφ₁) |>.mp h₂
    have : σ₁ ⊨ l₂ ⊓ Γ := by simp_all
    have ⟨_, hAgree₂', h₂'⟩ := e₂ τ |>.mp ⟨σ₁, hAgree, this⟩
    have : τ ⊨ φ₂ := agreeOn_semVars (hAgree₂'.subset hφ₂) |>.mp h₂'
    exact ⟨τ, PropAssignment.agreeOn_refl _, by simp_all⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    have : σ₂ ⊨ φ₁ := by simp_all
    have ⟨_, hAgree₁, h₁⟩ := e₁ τ |>.mpr ⟨σ₂, hAgree, this⟩
    have : τ ⊨ l₁ := agreeOn_semVars (hAgree₁.subset hL₁) |>.mp (satisfies_conj.mp h₁).left
    have : τ ⊨ Γ := agreeOn_semVars (hAgree₁.subset hΓ) |>.mp (satisfies_conj.mp h₁).right
    have : σ₂ ⊨ φ₂ := by simp_all
    have ⟨_, hAgree₁', h₁'⟩ := e₂ τ |>.mpr ⟨σ₂, hAgree, this⟩
    have : τ ⊨ l₂ := agreeOn_semVars (hAgree₁'.subset hL₂) |>.mp (satisfies_conj.mp h₁').left
    let τ' := τ.set s ⊤
    have hAgree' : τ'.agreeOn X τ := τ.agreeOn_set_of_not_mem _ hMem
    have : τ' ⊨ .var s := by simp
    have : τ' ⊨ l₁ := agreeOn_semVars (hAgree'.subset hL₁) |>.mpr (by assumption)
    have : τ' ⊨ l₂ := agreeOn_semVars (hAgree'.subset hL₂) |>.mpr (by assumption)
    have : τ' ⊨ Γ := agreeOn_semVars (hAgree'.subset hΓ) |>.mpr (by assumption)
    exact ⟨τ', τ.agreeOn_set_of_not_mem _ hMem, by simp_all⟩

end PropTerm