import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import ProofChecker.PropForm

open Finset

/-
A finset version of `PropForm.vars`.
-/

namespace PropForm

variable {ν : Type u} [DecidableEq ν]

/-- The unique evaluation function on formulas which extends `τ`. -/
@[simp]
def vars : PropForm ν → Finset ν
  | var x => {x}
  | tr => ∅
  | fls => ∅
  | neg φ => vars φ
  | conj φ₁ φ₂ => vars φ₁ ∪ vars φ₂
  | disj φ₁ φ₂ => vars φ₁ ∪ vars φ₂
  | impl φ₁ φ₂ => vars φ₁ ∪ vars φ₂
  | biImpl φ₁ φ₂ => vars φ₁ ∪ vars φ₂

theorem eval_ext {φ : PropForm ν} {v₁ v₂ : PropAssignment ν} (h : ∀ x ∈ φ.vars, v₁ x = v₂ x) :
    φ.eval v₁ = φ.eval v₂ := by
  induction φ <;> simp_all [eval, vars]

end PropForm

/-
This is the counting function for decomposable formulas, also known as POGs. The main theorem,
to be proved below, is that this really does count the number of models.
-/

namespace PropForm

def decomposable [DecidableEq ν]: PropForm ν → Prop
  | tr         => True
  | fls        => True
  | var _      => True
  | neg φ      => φ.decomposable
  | disj φ₁ φ₂ => φ₁.decomposable ∧ φ₂.decomposable ∧ ∀ v, ¬ (φ₁.eval v ∧ φ₂.eval v)
  | conj φ₁ φ₂ => φ₁.decomposable ∧ φ₂.decomposable ∧ (φ₁.vars ∩ φ₂.vars = ∅)
  | impl _ _   => False
  | biImpl _ _ => False

def countModels (s : Finset ν) : PropForm ν → Nat
  | tr         => 2^(card s)
  | fls        => 0
  | var _      => 2^(card s - 1)
  | neg φ      => 2^(card s) - φ.countModels s
  | disj φ₁ φ₂ => φ₁.countModels s + φ₂.countModels s
  | conj φ₁ φ₂ => (φ₁.countModels s) * (φ₂.countModels s) / 2^(card s)
  | impl _ _   => 0
  | biImpl _ _ => 0

end PropForm

/-
Propositional assignments and their restrictions to finsets.
-/

namespace PropAssignment

def defined_on (v : PropAssignment ν) (s : Finset ν) : Prop := ∀ ⦃n⦄, n ∉ s → v n = false

theorem defined_on_mono {v : PropAssignment ν} {s t : Finset ν} (h : s ⊆ t) :
    v.defined_on s → v.defined_on t :=
  fun h' _ hnnt => h' fun hns => hnnt (h hns)

variable [DecidableEq ν]

def restrict (v : PropAssignment ν) (s : Finset ν) : PropAssignment ν := fun x => if x ∈ s then v x else false

@[simp] theorem defined_on_restrict (v : PropAssignment ν) (s : Finset ν) :
    (v.restrict s).defined_on s := by intro n hns; rw [restrict, if_neg hns]

@[simp] theorem restrict_pos (v : PropAssignment ν) {x : ν} {s : Finset ν} (h : x ∈ s) :
    v.restrict s x = v x := by simp [restrict, h]

end PropAssignment

namespace PropForm

variable [DecidableEq ν]

theorem eval_restrict_vars (φ : PropForm ν) (v : PropAssignment ν) :
    φ.eval (v.restrict φ.vars) = φ.eval v :=
  eval_ext fun _ hx => v.restrict_pos hx

end PropForm

namespace Finset

variable [DecidableEq ν]

/-- The characteristic funbction of `s`. -/
def toPropAssignment (s : Finset ν) : PropAssignment ν := fun x => if x ∈ s then true else false

theorem toPropAssignment_eq_true {x : ν} (s : Finset ν) :
    s.toPropAssignment x = true ↔ x ∈ s := by
  rw [toPropAssignment]; split <;> simp_all

theorem toPropAssignment_eq_false {x : ν} (s : Finset ν) :
    s.toPropAssignment x = false ↔ x ∉ s := by
  simp [←toPropAssignment_eq_true]

end Finset

/-
Models of a propositional formula over a set of variables.

Note: we don't intend to use this theory computationally, so we use classical logic to declare decidable equality
on `PropAssignment ν`.
-/

variable [DecidableEq ν]

noncomputable instance : DecidableEq (PropAssignment ν) := fun _ _ => Classical.propDecidable _

namespace Finset

noncomputable def assignments (s : Finset ν) : Finset (PropAssignment ν) :=
  s.powerset.image (fun (t : Finset ν) (v : ν) => if v ∈ t then true else false)

theorem mem_assignments (s : Finset ν) (v : PropAssignment ν) : v ∈ assignments s ↔ v.defined_on s := by
  constructor
  . intro (h : v ∈ assignments s) i hnis
    rcases mem_image.mp h with ⟨t, ⟨htpows, rfl⟩⟩
    simp only [ite_eq_right_iff]
    rw [mem_powerset] at htpows
    intro (hit : i ∈ t)
    exact hnis (htpows hit)
  . intro h
    rw [assignments, mem_image]
    use s.filter (v . = true)
    constructor
    . rw [mem_powerset]; apply filter_subset
    . ext i; split
      . simp_all [mem_filter]
      . by_cases h' : i ∈ s <;> simp_all [PropAssignment.defined_on]

end Finset

namespace PropForm

noncomputable def models (φ : PropForm ν) (s : Finset ν) := s.assignments.filter (φ.eval .)

@[simp] theorem mem_models {φ : PropForm ν} {s : Finset ν} (v : PropAssignment ν) :
    v ∈ φ.models s ↔ v.defined_on s ∧ φ.eval v = true := by rw [models, mem_filter, mem_assignments]

theorem card_models_vars {φ : PropForm ν} {s : Finset ν} (h : φ.vars ⊆ s) :
    card (φ.models s) = card (φ.models φ.vars) * 2^(card s - card φ.vars) := by
  let f (p : PropAssignment ν × Finset ν) : PropAssignment ν :=
    fun x => if x ∈ φ.vars then p.1 x else p.2.toPropAssignment x
  have h1 : ((φ.models φ.vars).product (s \ φ.vars).powerset).image f = φ.models s := by
    ext v; simp only [mem_image, mem_product, mem_models, mem_powerset, Prod.exists]
    constructor
    { rintro ⟨v, t, ⟨⟨_, hevalv⟩, hh⟩, rfl⟩
      constructor
      . intro x hxns
        have : x ∉ φ.vars := fun h' => hxns (h h')
        dsimp; rw [if_neg this, toPropAssignment_eq_false]
        intro h'; apply hxns; exact subset_sdiff.mp hh |>.1 h'
      . rw [←hevalv]
        apply eval_ext
        intro x hx
        rw [if_pos hx] }
    intro ⟨hvdef, hevalv⟩
    use v.restrict φ.vars, (s \ φ.vars).filter (fun x => v x)
    constructor
    . constructor
      . constructor
        . simp
        . rw [eval_restrict_vars, hevalv]
      . apply filter_subset
    . ext x; dsimp; split
      . next h => rw [v.restrict_pos h]
      . next hmem =>
          unfold Finset.toPropAssignment
          by_cases hxs : x ∈ s <;> split <;> simp_all [@hvdef x]
  have h2 : Set.InjOn f <| (φ.models φ.vars).product (s \ φ.vars).powerset := by
    intro ⟨v1, t1⟩ h21 ⟨v2, t2⟩ h22 h23
    simp only [Set.mem_prod, mem_product, mem_coe, mem_models, Set.mem_preimage, mem_powerset, and_imp,
      subset_sdiff, Prod.forall, Prod.mk.injEq] at h21 h22 h23 |-
    constructor
    . ext x
      by_cases hx : x ∈ φ.vars
      . have := congr_fun h23 x
        simp [hx] at this; exact this
      . rw [h21.1.1 hx, h22.1.1 hx]
    . ext x
      simp at h21
      by_cases hx : x ∈ φ.vars
      . rw [eq_false (disjoint_right.mp h21.2.2 hx), eq_false (disjoint_right.mp h22.2.2 hx)]
      . have := congr_fun h23 x
        simp [hx] at this
        rw [←toPropAssignment_eq_true, this, toPropAssignment_eq_true]
  rw [←h1, card_image_of_injOn h2, card_product, card_powerset, card_sdiff h]

end PropForm

/-
The main theorem.
-/

theorem countModels_eq_card_models {φ : PropForm ν} {s : Finset ν} (hvars : φ.vars ⊆ s) (hdec : φ.decomposable) :
    φ.countModels s = card (φ.models s) := by
  sorry
