import ProofChecker.Model.PropVars

/-! Reasoning about definitional extensions. -/

namespace PropTerm

variable [DecidableEq ν]

theorem equivalentOver_disj_def {x : ν} {X : Set ν} (φ φ₁ φ₂ : PropTerm ν) :
    ↑φ.semVars ⊆ X → ↑φ₁.semVars ⊆ X → ↑φ₂.semVars ⊆ X → x ∉ X →
    equivalentOver X φ (φ ⊓ ((.var x)ᶜ ⊔ φ₁ ⊔ φ₂) ⊓ (.var x ⊔ φ₁ᶜ) ⊓ (.var x ⊔ φ₂ᶜ)) := by
  intro hSub hSub₁ hSub₂ hMem τ
  constructor
  case mp =>
    intro ⟨σ₁, hAgree, h₁⟩
    let σ₂ := σ₁.set x (φ₁.eval σ₁ || φ₂.eval σ₁)
    have hAgree₂₁ : σ₂.agreeOn X σ₁ := σ₁.agreeOn_set_of_not_mem _ hMem
    have : σ₂.agreeOn X τ := hAgree₂₁.trans hAgree
    have : σ₂ ⊨ φ := agreeOn_semVars (hAgree₂₁.subset hSub) |>.mpr h₁
    have : σ₂ ⊨ φ₁ ↔ σ₁ ⊨ φ₁ := agreeOn_semVars (hAgree₂₁.subset hSub₁)
    have : σ₂ ⊨ φ₂ ↔ σ₁ ⊨ φ₂ := agreeOn_semVars (hAgree₂₁.subset hSub₂)
    -- Some *heavy* aesops here.
    have : σ₂ ⊨ .var x ↔ σ₂ ⊨ φ₁ ∨ σ₂ ⊨ φ₂ := by aesop
    rw [iff_iff_not_or_and_or_not] at this
    have : σ₂ ⊨ (.var x)ᶜ ⊔ φ₁ ⊔ φ₂ := by aesop
    have : σ₂ ⊨ .var x ⊔ φ₁ᶜ := by aesop
    have : σ₂ ⊨ .var x ⊔ φ₂ᶜ := by aesop
    refine ⟨σ₂, by assumption, by simp_all [-satisfies_var]⟩
  case mpr =>
    intro ⟨σ₂, hAgree, h₂⟩
    exact ⟨σ₂, hAgree, by simp_all [-satisfies_var]⟩
    
-- LATER: If needed, prove that disj_def also has UEP.

end PropTerm