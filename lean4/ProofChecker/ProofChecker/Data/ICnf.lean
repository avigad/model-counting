import Mathlib.Tactic.Linarith

import ProofChecker.Data.HashMap.Lemmas
import ProofChecker.Data.HashSet
import ProofChecker.Model.ToMathlib
import ProofChecker.Model.PropTerm

abbrev Var := PNat

namespace Var

instance : ToString Var where
  toString x := toString x.val

instance : Hashable Var where
  hash v := hash v.val

end Var

/-! Literals -/

def ILit := { i : Int // i ≠ 0 }
  deriving DecidableEq, Repr

namespace ILit

def mkPos (x : Var) : ILit :=
  ⟨Int.ofNat x.val, by simp⟩

def mkNeg (x : Var) : ILit :=
  ⟨-Int.ofNat x.val, by simp⟩

def mk (x : Var) (p : Bool) : ILit :=
  if p then mkPos x else mkNeg x

def var (l : ILit) : Var :=
  ⟨Int.natAbs l.val, Int.natAbs_pos.mpr l.property⟩

def polarity (l : ILit) : Bool :=
  (0 : Int) < l.val

def negate (l : ILit) : ILit :=
  ⟨-l.val, Int.neg_ne_zero.mpr l.property⟩

instance : Neg ILit := ⟨negate⟩

instance : ToString ILit where
  toString l := if l.polarity then s!"{l.var}" else s!"-{l.var}"

/-! Theorems about `ILit` -/

@[simp]
theorem var_mkPos (x :  Var) : var (mkPos x) = x :=
  Subtype.ext (Int.natAbs_ofNat x.val)

@[simp]
theorem var_mkNeg (x : Var) : var (mkNeg x) = x := by
  apply Subtype.ext
  simp [var, mkNeg]
  rfl
  
@[simp]
theorem var_mk (x : Var) (p : Bool) : var (mk x p) = x := by
  dsimp [mk]; split <;> simp

@[simp]
theorem polarity_mkPos (x : Var) : polarity (mkPos x) = true := by
  simp [polarity, mkPos]

@[simp]
theorem polarity_mkNeg (x : Var) : polarity (mkNeg x) = false := by
  simp [polarity, mkNeg]

@[simp]
theorem polarity_mk (x : Var) (p : Bool) : polarity (mk x p) = p := by
  dsimp [mk]; split <;> simp_all

@[simp]
theorem var_negate (l : ILit) : (-l).var = l.var := by
  simp only [var, Neg.neg, negate]
  apply Subtype.ext
  apply Int.natAbs_neg

theorem polarity_eq {l₁ l₂ : ILit} :
    l₁.polarity = l₂.polarity ↔ ((0 : Int) < l₁.val ↔ (0 : Int) < l₂.val) := by
  simp [polarity]

@[simp]
theorem polarity_negate (l : ILit) : (-l).polarity = !l.polarity := by
  rw [Bool.eq_bnot_to_not_eq, polarity_eq]
  intro hEq
  exact l.property (Int.eq_zero_of_lt_neg_iff_lt _ hEq)

@[ext]
theorem ext {l₁ l₂ : ILit} : l₁.var = l₂.var → l₁.polarity = l₂.polarity → l₁ = l₂ := by
  /- Strip type alias. -/
  suffices ∀ {l₁ l₂ : Int}, l₁.natAbs = l₂.natAbs → (0 < l₁ ↔ 0 < l₂) → l₁ = l₂ by
    intro h₁ h₂
    apply Subtype.ext
    apply this
    . exact Subtype.mk_eq_mk.mp h₁
    . exact polarity_eq.mp h₂
  intro l₁ l₂ h₁ h₂
  cases Int.natAbs_eq_natAbs_iff.mp h₁
  . assumption
  next h =>
    rw [h] at h₂
    have : l₂ = 0 := Int.eq_zero_of_lt_neg_iff_lt l₂ h₂
    simp [this, h]

@[simp]
theorem eta (l : ILit) : mk l.var l.polarity = l := by
  apply ext <;> simp

@[simp]
theorem eta_neg (l : ILit) : mk l.var (!l.polarity) = -l := by
  apply ext <;> simp

def toPropForm (l : ILit) : PropForm Var :=
  if l.polarity then .var l.var else .neg (.var l.var)

def toPropTerm (l : ILit) : PropTerm Var :=
  if l.polarity then .var l.var else (.var l.var)ᶜ

@[simp]
theorem mk_toPropForm (l : ILit) : ⟦l.toPropForm⟧ = l.toPropTerm := by
  dsimp [toPropForm, toPropTerm]
  cases l.polarity <;> simp

open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {l : ILit} :
    τ ⊨ l.toPropTerm ↔ τ l.var = l.polarity := by
  dsimp [toPropTerm, var, polarity]
  aesop
  
theorem satisfies_neg {τ : PropAssignment Var} {l : ILit} :
    τ ⊨ (-l).toPropTerm ↔ τ ⊭ l.toPropTerm := by
  simp [satisfies_iff]

theorem satisfies_set [DecidableEq ν] (τ : PropAssignment Var) (l : ILit) :
    τ.set l.var l.polarity ⊨ l.toPropTerm := by
  simp [satisfies_iff, τ.set_get]

theorem eq_of_flip {τ : PropAssignment Var} {l : ILit} {x : Var} {p : Bool} :
    τ ⊭ l.toPropTerm → τ.set x p ⊨ l.toPropTerm → l = mk x p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = var l
  . rw [hEq, τ.set_get] at hSet
    simp [*]
  . exfalso; exact h (τ.set_get_of_ne p hEq ▸ hSet)

end ILit

/-! Clauses -/

abbrev IClause := Array ILit

namespace IClause

def vars (C : IClause) : HashSet Var :=
  C.foldr (init := .empty Var) fun l acc => acc.insert l.var

instance : BEq IClause :=
  inferInstanceAs (BEq IClause)

instance : ToString IClause where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

/-! Theorems about `IClause` -/

def toPropTerm (C : IClause) : PropTerm Var :=
  C.data.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ)
  
open PropTerm

theorem satisfies_iff {τ : PropAssignment Var} {C : IClause} :
    τ ⊨ C.toPropTerm ↔ ∃ l ∈ C.data, τ ⊨ l.toPropTerm := by
  rw [toPropTerm]
  induction C.data <;> simp_all
  
theorem tautology_iff (C : IClause) :
    C.toPropTerm = ⊤ ↔ ∃ l₁ ∈ C.data, ∃ l₂ ∈ C.data, l₁ = -l₂ := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    refine not_imp_not.mp ?_
    simp only [not_exists, not_and]
    unfold toPropTerm -- :( have to do it because no induction principle for arrays
    induction C.data with
    | nil => simp
    | cons l₀ ls ih =>
      -- crazy list-array induction boilerplate
      have : ls.foldr (init := ⊥) (fun l φ => l.toPropTerm ⊔ φ) = toPropTerm ls.toArray := by
        simp [toPropTerm]
      simp only [List.foldr_cons, this] at *
      -- end boilerplate
      intro hCompl hEq
      specialize ih fun l₁ h₁ l₂ h₂ => hCompl l₁ (by simp [h₁]) l₂ (by simp [h₂])
      simp only [PropTerm.eq_top_iff, satisfies_disj, not_forall] at hEq ih
      have ⟨τ₀, h₀⟩ := ih
      have := hEq τ₀
      have : τ₀ ⊨ l₀.toPropTerm := by tauto
      let τ₁ := τ₀.set l₀.var !l₀.polarity
      have : τ₁ ⊭ l₀.toPropTerm := by simp [ILit.satisfies_iff]
      have : τ₁ ⊭ toPropTerm ls.toArray := fun h => by
        have ⟨lₛ, hₛ, hτ⟩ := satisfies_iff.mp h
        simp only [satisfies_iff, not_exists, not_and] at h₀
        have : τ₀ ⊭ lₛ.toPropTerm := h₀ lₛ hₛ
        have : lₛ = ILit.mk l₀.var !l₀.polarity := ILit.eq_of_flip this hτ
        have : lₛ = -l₀ := by simp [this]
        simp at hₛ
        apply hCompl lₛ (List.mem_cons_of_mem _ hₛ) l₀ (List.mem_cons_self _ _) this
      have := hEq τ₁
      tauto
  case mpr =>
    intro ⟨l₁, h₁, l₂, h₂, hEq⟩
    ext τ
    rw [satisfies_iff]
    by_cases hτ : τ ⊨ l₂.toPropTerm
    . aesop
    . have : τ ⊨ l₁.toPropTerm := by
        rw [hEq, ILit.satisfies_neg]
        assumption
      tauto

end IClause

/-! CNF -/

abbrev ICnf := Array IClause

namespace ICnf

def vars (φ : ICnf) : HashSet Var :=
  φ.foldr (init := .empty Var) fun C acc => acc.union C.vars

instance : ToString ICnf where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

/-! Theorems about `ICnf` -/

def toPropTerm (φ : ICnf) : PropTerm Var :=
  φ.data.foldr (init := ⊤) (fun l φ => l.toPropTerm ⊓ φ)

open PropTerm
  
theorem satisfies_iff {τ : PropAssignment Var} {φ : ICnf} :
    τ ⊨ φ.toPropTerm ↔ ∀ C ∈ φ.data, τ ⊨ C.toPropTerm := by
  rw [toPropTerm]
  induction φ.data <;> simp_all

end ICnf

/-! Partial assignments -/

/-- A partial assignment to propositional variables. -/
-- TODO: Using `HashMap` for this is cache-inefficient but I don't have time to verify better
-- structures rn
abbrev PartPropAssignment := HashMap Var Bool

namespace PartPropAssignment

/-- Interpret the assignment (x ↦ ⊤, y ↦ ⊥) as x ∧ ¬y, for example. -/
def toPropTerm (τ : PartPropAssignment) : PropTerm Var :=
  τ.fold (init := ⊤) fun acc x v => acc ⊓ if v then .var x else (.var x)ᶜ
  
open PropTerm
  
theorem satisfies_iff (τ : PartPropAssignment) (σ : PropAssignment Var) :
    σ ⊨ τ.toPropTerm ↔ ∀ x p, τ.find? x = some p → σ x = p :=
  ⟨mp, mpr⟩
where
  mp := fun h => by
    intro x p? hFind
    have ⟨φ, hφ⟩ := τ.fold_of_mapsTo_of_comm
      (init := ⊤) (f := fun acc x v => acc ⊓ if v then PropTerm.var x else (PropTerm.var x)ᶜ)
      hFind ?comm
    case comm => 
      intros
      dsimp
      ac_rfl
    rw [toPropTerm, hφ] at h
    aesop

  mpr := fun h => by
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ x p hφ hFind
    rw [satisfies_conj]
    refine ⟨hφ, ?_⟩
    have := h _ _ hFind
    split <;> simp [*]

end PartPropAssignment

namespace IClause

/-- Reduces a clause by a partial assignment. Returns `none` if it became satisfied,
otherwise `some C'` where `C'` is the reduced clause. -/
def reduce (C : IClause) (τ : PartPropAssignment) : Option IClause :=
  C.foldlM (init := #[]) fun acc l =>
    match τ.find? l.var with
    | some v => if v == l.polarity then none else acc
    | none => some <| acc.push l
    
-- theorem reduce_thm (C C' : IClause) (τ : PartPropAssignment) :
--   reduce C τ = some C' → C.toPropTerm ⊓ τ.toPropTerm ≤ C'.toPropTerm := by

/-- When `C` is not a tautology, return the smallest assignment falsifying it. When it is not,
return an undetermined assignment. -/
def toFalsifyingAssignment (C : IClause) : PartPropAssignment :=
  C.foldl (init := .empty) fun acc l => acc.insert l.var !l.polarity

theorem toFalsifyingAssignment_characterization (C : IClause) : C.toPropTerm ≠ ⊤ →
    (∀ i : Fin C.size, C.toFalsifyingAssignment.find? C[i].var = some !C[i].polarity) ∧
    (∀ x p, C.toFalsifyingAssignment.find? x = some p → (ILit.mk x !p) ∈ C.data) := by
  intro hTauto
  have := C.foldl_induction
    (motive := fun (sz : Nat) (τ : PartPropAssignment) =>
      (∀ i : Fin C.size, i < sz → τ.find? C[i].var = some !C[i].polarity) ∧
      (∀ x p, τ.find? x = some p → (ILit.mk x !p) ∈ C.data))
    (init := .empty)
    (f := fun acc l => acc.insert l.var !l.polarity)
    (h0 := by simp)
    (hf := by
      intro sz τ ⟨ih₁, ih₂⟩
      refine ⟨?step₁, ?step₂⟩
      case step₁ =>
        intro i hLt
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt) with
        | inl h =>
          by_cases hEq : C[sz].var = C[i].var
          . have : C[sz].polarity = C[i].polarity := by
              by_contra hPol
              have : C[sz] = -C[i] := by
                apply ILit.ext <;> simp_all
              apply hTauto
              rw [tautology_iff]
              exact ⟨C[sz], Array.get_mem_data _ _, C[i], Array.get_mem_data _ _, this⟩
            have : C[sz] = C[i] := ILit.ext hEq this
            simp_all [HashMap.find?_insert]
          . simp only [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr hEq), ih₁ i h]
        | inr h =>
          simp [h]
          rw [HashMap.find?_insert _ _ LawfulBEq.rfl]
      case step₂ =>
        intro x p hFind
        by_cases hEq : C[sz].var = x
        . rw [← hEq, HashMap.find?_insert _ _ (LawfulBEq.rfl)] at hFind
          injection hFind with hFind
          rw [← hEq, ← hFind]
          simp [Array.getElem_mem_data]
        . rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _|>.mpr hEq)] at hFind
          apply ih₂ _ _ hFind)
  dsimp [toFalsifyingAssignment]
  exact ⟨fun i => this.left i i.isLt, this.right⟩

theorem toFalsifyingAssignment_ext (C : IClause) : C.toPropTerm ≠ ⊤ →
    l ∈ C.data ↔ (toFalsifyingAssignment C).find? l.var = some !l.polarity := by
  sorry

theorem toPropTerm_toFalsifyingAssignment (C : IClause) : C.toPropTerm ≠ ⊤ →
    C.toFalsifyingAssignment.toPropTerm = C.toPropTermᶜ := by
  sorry

end IClause