import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import ProofChecker.Data.Pog

open Finset

/-
This is the counting function for decomposable formulas, also known as POGs. The main theorem,
to be proved below, is that this really does count the number of models.
-/

namespace PropForm

def countModels (nVars : Nat) : PropForm ν → Nat
  | tr         => 2^nVars
  | fls        => 0
  | var _      => 2^(nVars - 1)
  | neg φ      => 2^nVars - φ.countModels nVars
  | disj φ ψ   => φ.countModels nVars + ψ.countModels nVars
  | conj φ ψ   => φ.countModels nVars * ψ.countModels nVars / 2^nVars
  | impl _ _   => 0
  | biImpl _ _ => 0

end PropForm

/-
Propositional assignments and their restrictions to finsets.
-/

namespace PropAssignment

def defined_on (v : PropAssignment ν) (s : Finset ν) : Prop := ∀ ⦃x⦄, x ∉ s → v x = false

theorem eq_false_of_defined_on {v : PropAssignment ν} {s : Finset ν} {x : ν}
    (h : v.defined_on s) (h' : ¬ x ∈ s) : v x = false := h h'

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

theorem injective_toPropAssignment : Function.Injective (@toPropAssignment ν _) := by
  intro s1 s2 heq
  ext x
  have := congr_fun heq x
  rw [←s1.toPropAssignment_eq_true, this, s2.toPropAssignment_eq_true]

end Finset

/-
Models of a propositional formula over a set of variables.

Note: we don't intend to use this theory computationally, so we use classical logic to declare
decidable equality on `PropAssignment ν`.
-/

variable [DecidableEq ν]

noncomputable instance : DecidableEq (PropAssignment ν) := fun _ _ => Classical.propDecidable _

namespace Finset

noncomputable def assignments (s : Finset ν) : Finset (PropAssignment ν) :=
  s.powerset.image toPropAssignment

@[simp] theorem mem_assignments (s : Finset ν) (v : PropAssignment ν) :
    v ∈ assignments s ↔ v.defined_on s := by
  simp only [assignments, mem_image, mem_powerset]
  constructor
  . rintro ⟨t, ht1, rfl⟩ x hx
    rw [toPropAssignment_eq_false]
    intro h; exact hx (ht1 h)
  . intro h
    use s.filter (v . = true)
    simp only [filter_subset, true_and]
    ext x
    simp only [toPropAssignment, mem_filter]
    by_cases hx : x ∈ s
    . cases (v x) <;> simp [hx]
    . simp [hx, h hx]

theorem card_assignments (s : Finset ν) : card (assignments s) = 2^(card s) := by
  rw [assignments, card_image_of_injective _ injective_toPropAssignment, card_powerset]

end Finset

namespace PropForm

noncomputable def models (φ : PropForm ν) (s : Finset ν) := s.assignments.filter (φ.eval .)

@[simp] theorem mem_models {φ : PropForm ν} {s : Finset ν} (v : PropAssignment ν) :
    v ∈ φ.models s ↔ v.defined_on s ∧ φ.eval v = true :=
  by rw [models, mem_filter, mem_assignments]

@[simp] theorem card_models_tr (s : Finset ν) : card ((tr : PropForm ν).models s) = 2^(card s) := by
  simp [models, card_assignments]

@[simp] theorem card_models_fls (s : Finset ν) : card ((fls : PropForm ν).models s) = 0 := by
  simp [models, card_assignments]

@[simp] theorem card_models_var {x : ν} {s : Finset ν} (hxs : x ∈ s) :
    card ((var x).models s) = 2^(card s - 1) := by
  let f (v : PropAssignment ν) : PropAssignment ν := fun x' => if x' = x then true else v x'
  have h1 : (var x).models s = (assignments (s.erase x)).image f := by
    ext v; simp only [mem_models, eval, mem_image]
    constructor
    . intro ⟨hvdef, hvx⟩
      use fun x' => if x' = x then false else v x'
      constructor
      . rw [mem_assignments]
        intro x' hx'
        rw [mem_erase, not_and] at hx'; dsimp
        split <;> simp_all [v.eq_false_of_defined_on hvdef]
      . ext x'
        split <;> simp_all [v.eq_false_of_defined_on hvdef]
    . rintro ⟨v', hv', rfl⟩
      rw [mem_assignments] at hv'
      constructor
      . intro x' hx'
        have : x' ≠ x := by rintro rfl; contradiction
        dsimp; rw [if_neg this, v'.eq_false_of_defined_on hv']
        rw [mem_erase, not_and_or]; right; exact hx'
      . simp
  have h2 : Set.InjOn f (assignments (s.erase x)) := by
    intro v1 hv1 v2 hv2 heq
    simp only [mem_coe, mem_assignments] at hv1 hv2
    ext x'
    have := congr_fun heq x'
    clear h1 heq; revert f; dsimp
    split
    . simp_all
      have : x ∉ erase s x := by simp [mem_erase]
      rw [hv1 this, hv2 this]
    . exact id
  rw [h1, card_image_of_injOn h2, card_assignments, card_erase_of_mem hxs]

@[simp] theorem card_models_disj_disjoint {φ ψ : PropForm ν} (s : Finset ν)
      (h : ∀ v, ¬ (φ.eval v ∧ ψ.eval v)) :
    card ((φ.disj ψ).models s) = card (φ.models s) + card (ψ.models s) := by
  have : (φ.disj ψ).models s = (φ.models s) ∪ (ψ.models s) := by
    ext v; simp only [mem_models, eval, Bool.or_eq_true, mem_union]
    rw [and_or_left]
  rw [this, card_disjoint_union]
  rw [disjoint_iff_ne]
  rintro v hv1 _ hv2 rfl
  apply h v
  rw [mem_models] at hv1 hv2
  rw [hv1.2, hv2.2]; simp

@[simp] theorem card_models_neg (φ : PropForm ν) (s : Finset ν) :
    card (φ.neg.models s) = 2^(card s) - card (φ.models s) := by
  symm; apply Nat.sub_eq_of_eq_add
  rw [←card_assignments s]
  have : assignments s = φ.neg.models s ∪ φ.models s := by
    ext v; simp only [mem_assignments, mem_union, mem_models, eval, Bool.bnot_eq_to_not_eq,
      Bool.not_eq_true]
    rw [←and_or_left]; cases (eval v φ) <;> simp
  rw [this, card_disjoint_union]
  rw [disjoint_iff_ne]
  rintro v hv1 _ hv2 rfl
  rw [mem_models] at hv2
  rw [mem_models, eval, hv2.2] at hv1
  simp at hv1

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
    simp only [Set.mem_prod, mem_product, mem_coe, mem_models, Set.mem_preimage, mem_powerset,
      and_imp, subset_sdiff, Prod.forall, Prod.mk.injEq] at h21 h22 h23 |-
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

theorem card_models_conj_aux {φ ψ: PropForm ν} (hdisj : φ.vars ∩ ψ.vars = ∅) :
    card ((φ.conj ψ).models (φ.conj ψ).vars) =
      card (φ.models φ.vars) * card (ψ.models ψ.vars) := by
  let f (p : PropAssignment ν × PropAssignment ν) : PropAssignment ν :=
    fun x => if x ∈ φ.vars then p.1 x else p.2 x
  have h1 : ((φ.models φ.vars).product (ψ.models ψ.vars)).image f =
    (φ.conj ψ).models (φ.vars ∪ ψ.vars) := by
    ext v; simp [mem_image, mem_product, mem_models, Prod.exists, eval, Bool.and_eq_true]
    constructor
    . rintro ⟨v1, v2, ⟨⟨_, heval1⟩, ⟨hdef2, heval2⟩⟩, rfl⟩
      constructor
      . intro x hx
        rw [mem_union, not_or] at hx
        dsimp; rw [if_neg hx.1, hdef2 hx.2]
      . constructor
        . rw [←heval1]; apply eval_ext
          intro x hx; rw [if_pos hx]
        . rw [←heval2]; apply eval_ext
          intro x hx
          simp only [eq_empty_iff_forall_not_mem, mem_inter, not_and'] at hdisj
          have hx' : x ∉ φ.vars := hdisj _ hx
          rw [if_neg hx']
    . intro ⟨hdef, heval1, heval2⟩
      use fun x => if x ∈ φ.vars then v x else false
      use fun x => if x ∈ ψ.vars then v x else false
      dsimp
      constructor
      . constructor
        . constructor
          . intro x hx; dsimp; rw [if_neg hx]
          . rw [←heval1]
            apply eval_ext; intro x hx; rw [if_pos hx]
        . constructor
          . intro x hx; dsimp; rw [if_neg hx]
          . rw [←heval2]
            apply eval_ext; intro x hx; rw [if_pos hx]
      . ext x
        have := @hdef x
        split <;> simp_all
  have h2 : Set.InjOn f <| (φ.models φ.vars).product (ψ.models ψ.vars) := by
    intro ⟨p11, p12⟩ hp1 ⟨p21, p22⟩ hp2
    simp only [coe_product, Set.mem_prod, mem_coe, mem_models] at hp1 hp2
    clear h1; revert f; dsimp; intro h
    rw [Prod.mk.injEq]
    constructor
    . ext x
      have := congr_fun h x
      by_cases h' : x ∈ φ.vars <;> simp_all
      rw [hp1.1.1 h', hp2.1.1 h']
    . ext x
      have := congr_fun h x
      by_cases h' : x ∈ φ.vars <;> simp_all
      simp only [eq_empty_iff_forall_not_mem, mem_inter, not_and] at hdisj
      rw [hp1.2.1 (hdisj _ h'), hp2.2.1 (hdisj _ h')]
  rw [vars, ←h1, card_image_of_injOn h2, card_product]

@[simp] theorem card_models_conj {φ ψ : PropForm ν} {s : Finset ν}
      (hsub : φ.vars ∪ ψ.vars ⊆ s) (hdisj : vars φ ∩ vars ψ = ∅) :
    card ((φ.conj ψ).models s) = card (φ.models s) * card (ψ.models s) / 2^(card s):= by
  symm; apply Nat.div_eq_of_eq_mul_left
  . apply pow_pos; apply zero_lt_two
  have hφ := union_subset_left hsub
  have hψ := union_subset_right hsub
  have card_un := card_disjoint_union (disjoint_iff_inter_eq_empty.mpr hdisj)
  have aux : card (vars ψ) ≤ card s - card (vars φ) := by
    apply Nat.le_sub_of_add_le
    rw [add_comm, ←card_un]
    exact card_le_of_subset hsub
  have : (φ.conj ψ).vars ⊆ s := by rw [vars, union_subset_iff]; exact ⟨hφ, hψ⟩
  rw [card_models_vars hφ, card_models_vars hψ, card_models_vars this, card_models_conj_aux hdisj]
  rw [mul_right_comm]; simp only [mul_assoc, ←pow_add]
  rw [←Nat.sub_add_comm (card_le_of_subset hψ)]
  rw [Nat.add_sub_assoc aux, add_comm (card s)]
  rw [vars, card_un, tsub_tsub]

/-
The main theorem.
-/

theorem countModels_eq_card_models {φ : PropForm ν} {s : Finset ν}
      (hvars : φ.vars ⊆ s) (hdec : φ.decomposable) :
    φ.countModels s.card = card (φ.models s) := by
  induction φ
  case var x      =>
    rw [vars, singleton_subset_iff] at hvars
    rw [countModels, card_models_var hvars]
  case tr         => simp [countModels]
  case fls        => simp [countModels]
  case neg φ ih   =>
    rw [vars] at hvars
    rw [decomposable] at hdec
    rw [countModels, card_models_neg φ, ih hvars hdec]
  case conj φ ψ ihφ ihψ =>
    rw [vars] at hvars
    have hφ := union_subset_left hvars
    have hψ := union_subset_right hvars
    rw [decomposable] at hdec
    rw [countModels, card_models_conj hvars hdec.2.2, ihφ hφ hdec.1, ihψ hψ hdec.2.1]
  case disj φ ψ ihφ ihψ =>
    rw [vars, union_subset_iff] at hvars
    rw [decomposable] at hdec
    rw [countModels, card_models_disj_disjoint s hdec.2.2, ihφ hvars.1 hdec.1, ihψ hvars.2 hdec.2.1]
  case impl  _    => rw [decomposable] at hdec; contradiction
  case biImpl _ _ => rw [decomposable] at hdec; contradiction

end PropForm