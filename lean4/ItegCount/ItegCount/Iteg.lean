import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

/- itegs-/

inductive IteElt
  | tr                 : IteElt
  | fls                : IteElt
  | var  (i : Nat)     : IteElt
  | ite (c t f : Nat) : IteElt
deriving Repr, DecidableEq, Inhabited

open IteElt

inductive eqCases (iteElt : IteElt): Prop where
  | eq_tr                : iteElt = tr → eqCases iteElt
  | eq_fls               : iteElt = fls → eqCases iteElt
  | eq_var (k : Nat)     : iteElt = var k → eqCases iteElt
  | eq_ite (c t f : Nat) : iteElt = ite c t f → eqCases iteElt

open eqCases
theorem IteElt.toEqCases (iteElt : IteElt) : eqCases iteElt := by
  cases iteElt
  . exact eq_tr rfl
  . exact eq_fls rfl
  . exact eq_var _ rfl
  . exact eq_ite _ _ _ rfl

/- Assignments of truth assignments to variables. -/

def Assignment : Type := Nat → Bool

noncomputable instance : DecidableEq Assignment := fun _ _ => Classical.propDecidable _

namespace Assignment

@[ext] theorem ext (v1 v2 : Assignment) (h : ∀ x, v1 x = v2 x) : v1 = v2 := funext h

def defined_on (v : Assignment) (s : Finset Nat) := ∀ ⦃n⦄, n ∉ s → v n = false

theorem defined_on_mono {v : Assignment} {s t : Finset Nat} (h : s ⊆ t) :
    v.defined_on s → v.defined_on t :=
  fun h' _ hnnt => h' fun hns => hnnt (h hns)

def update (n : Nat) (b : Bool) (v : Assignment) : Assignment := fun i => if i = n then b else v i

@[simp] theorem update_self (n : Nat) (b : Bool) (v : Assignment) :
  update n b v n = b := by simp [update]

@[simp] theorem update_pos {n : Nat} {i : Nat} (h : i = n) (b : Bool) (v : Assignment) :
  update n b v i = b := by simp [update, h]

@[simp] theorem update_neg {n : Nat} {i : Nat} (h : i ≠ n) (b : Bool) (v : Assignment) :
  update n b v i = v i := by simp [update, h]

theorem update_update (n : Nat) (b₁ b₂ : Bool) (v : Assignment) :
    update n b₁ (update n b₂ v) = update n b₁ v := by
  ext n'
  by_cases h : n' = n
  . rw [←h, update_self, update_self]
  . rw [update_neg h, update_neg h, update_neg h]

theorem update_same (n : Nat) (v : Assignment) : update n (v n) v = v := by
  ext n'
  by_cases h : n' = n
  . rw [←h, update_self]
  . rw [update_neg h]

theorem defined_on_update {v : Assignment} {s : Finset Nat}
      (h : v.defined_on s) (n : Nat) (b : Bool) :
    defined_on (v.update n b) (insert n s) := by
  intros n' hn'
  rw [Finset.mem_insert, not_or] at hn'
  rw [update_neg hn'.1]
  exact h hn'.2

end Assignment

def IteElt.bounded : IteElt → Nat → Prop
  | tr,        _ => true
  | fls,       _ => true
  | var _,     _ => true
  | ite _ t f, b => t < b ∧ f < b

def Iteg := { I : Array IteElt // ∀ (i : Fin I.size), I[i].bounded i }

namespace Iteg

theorem t_lt (I : Iteg) (i : Fin I.val.size) {c t f : Nat} (h : I.val[i] = ite c t f) :
    t < I.val.size :=
  h ▸ I.property i |>.left.trans i.isLt

theorem f_lt (I : Iteg) (i : Fin I.val.size) {c t f : Nat} (h : I.val[i] = ite c t f) :
    f < I.val.size :=
  h ▸ I.property i |>.right.trans i.isLt

/--
`eval I v i` evaluates node `i` with respect to truth assignment `v`.
-/
def eval (I : Iteg) (v : Assignment) (i : Fin I.val.size) : Bool :=
  match I.val[i], I.property i with
    | tr,               _        => true
    | fls,              _        => false
    | var k,            _        => v k
    | IteElt.ite c t f, ⟨ht, hf⟩ =>
      cond (v c) (I.eval v ⟨t, ht.trans i.isLt⟩) (I.eval v ⟨f, hf.trans i.isLt⟩)

theorem eval_tr {I : Iteg} (v : Assignment) (i : Fin I.val.size) (h : I.val[i] = tr) :
    I.eval v i = true := by unfold eval; split <;> simp_all only

theorem eval_fls {I : Iteg} (v : Assignment) (i : Fin I.val.size) (h : I.val[i] = fls) :
    I.eval v i = false := by unfold eval; split <;> simp_all only

theorem eval_var {I : Iteg} (v : Assignment) (i : Fin I.val.size) (h : I.val[i] = var k) :
    I.eval v i = v k := by
  unfold eval; split <;> simp_all only
  cases h; rfl

theorem eval_ite {I : Iteg} (v : Assignment) (i : Fin I.val.size) (h : I.val[i] = ite c t f) :
    I.eval v i = cond (v c) (I.eval v ⟨t, I.t_lt i h⟩) (I.eval v ⟨f, I.f_lt i h⟩) := by
  conv => lhs; unfold eval
  split <;> simp_all only
  next h' _ => cases h'; simp

/--
`vars I i` returns the finset of variables that node `i` depends on.
-/
def vars (I : Iteg) (i : Fin I.val.size) : Finset Nat :=
  match I.val[i], I.property i with
    | tr,               _        => ∅
    | fls,              _        => ∅
    | var k,            _        => {k}
    | IteElt.ite c t f, ⟨ht, hf⟩ =>
        insert c (I.vars ⟨t, ht.trans i.isLt⟩ ∪ I.vars ⟨f, hf.trans i.isLt⟩)

theorem vars_tr {I : Iteg} (i : Fin I.val.size) (h : I.val[i] = tr) :
    I.vars i = ∅ := by unfold vars; split <;> simp_all only

theorem vars_fls {I : Iteg} (i : Fin I.val.size) (h : I.val[i] = fls) :
    I.vars i = ∅ := by unfold vars; split <;> simp_all only

theorem vars_var {I : Iteg} (i : Fin I.val.size) (h : I.val[i] = var k) :
    I.vars i = {k} := by
  unfold vars; split <;> simp_all only
  cases h; rfl

theorem vars_ite {I : Iteg} (i : Fin I.val.size) (h : I.val[i] = ite c t f) :
    I.vars i = insert c (I.vars ⟨t, I.t_lt i h⟩ ∪ I.vars ⟨f, I.f_lt i h⟩) := by
  conv => lhs; unfold vars
  split <;> simp_all only
  next h' _ => cases h'; simp

/--
`count I j` counts the number of models of line `j` of iteg `I`, assuming `numVars` variables in
total.
-/
def count (I : Iteg) (numVars : Nat) (i : Fin I.val.size) : Nat :=
  match I.val[i], I.property i with
    | tr,               _        => 2^numVars
    | fls,              _        => 0
    | var k,            _        => 2^(numVars - 1)
    | IteElt.ite _ t f, ⟨ht, hf⟩ =>
        (I.count numVars ⟨t, ht.trans i.isLt⟩ + I.count numVars ⟨f, hf.trans i.isLt⟩)/2

theorem count_tr {I : Iteg} (numVars : Nat) (i : Fin I.val.size) (h : I.val[i] = tr) :
    I.count numVars i = 2^numVars := by unfold count; split <;> simp_all only

theorem count_fls {I : Iteg} (numVars : Nat) (i : Fin I.val.size) (h : I.val[i] = fls) :
    I.count numVars i = 0 := by unfold count; split <;> simp_all only

theorem count_var {I : Iteg} (numVars : Nat) (i : Fin I.val.size) (h : I.val[i] = var k) :
    I.count numVars i = 2^(numVars - 1) := by
  unfold count; split <;> simp_all only

theorem count_ite {I : Iteg} {c t f : Nat} (numVars : Nat) (i : Fin I.val.size)
      (h : I.val[i] = ite c t f) :
    I.count numVars i = (I.count numVars ⟨t, I.t_lt i h⟩ + I.count numVars ⟨f, I.f_lt i h⟩) / 2 := by
  conv => lhs; unfold count
  split <;> simp_all only
  next h' _ => cases h'; simp

/- free itegs -/

def free (I : Iteg) : Prop :=
∀ i : Fin I.val.size, match I.val[i], I.property i with
       | tr,               _        => true
       | fls,              _        => true
       | var _,            _        => true
       | IteElt.ite c t f, ⟨ht, hf⟩ =>
           c ∉ I.vars ⟨t, ht.trans i.isLt⟩ ∧ c ∉ I.vars ⟨f, hf.trans i.isLt⟩

theorem free_ite {I : Iteg} (freeI : free I) {c t f : Nat} (i : Fin I.val.size)
      (h : I.val[i] = ite c t f) :
    c ∉ I.vars ⟨t, I.t_lt i h⟩ ∧ c ∉ I.vars ⟨f, I.f_lt i h⟩ := by
  have := freeI i
  revert this
  split <;> simp_all only
  next h' _ => cases h'; exact id

/- counting models assignments -/

open Finset Assignment

noncomputable def models (s : Finset Nat) : Finset Assignment :=
  s.powerset.image (fun (t : Finset Nat) (v : Nat) => if v ∈ t then true else false)

theorem mem_models (s : Finset Nat) (v : Assignment) : v ∈ models s ↔ v.defined_on s := by
  constructor
  . intro (h : v ∈ models s) i hnis
    rcases mem_image.mp h with ⟨t, ⟨htpows, rfl⟩⟩
    simp only [ite_eq_right_iff]
    rw [mem_powerset] at htpows
    intro (hit : i ∈ t)
    exact hnis (htpows hit)
  . intro h
    rw [models, mem_image]
    use s.filter (v . = true)
    constructor
    . rw [mem_powerset]; apply filter_subset
    . ext i; split
      . simp_all [mem_filter]
      . by_cases h' : i ∈ s <;> simp_all [Assignment.defined_on]

theorem models_insert (s : Finset Nat) (n : Nat) :
    models (insert n s) = models s ∪ (models s).image (Assignment.update n true) := by
  ext v; simp only [Finset.mem_union, Finset.mem_image, mem_models]
  constructor
  . intro h'
    cases h : v n
    . left
      intro n' hn'
      by_cases heq : n' = n
      . rw [heq, h]
      . apply h'
        rw [mem_insert, not_or]
        exact ⟨heq, hn'⟩
    . right
      use v.update n false
      constructor
      . intro n' hn'
        by_cases heq : n' = n
        . rw [update_pos heq]
        . rw [update_neg heq]
          apply h'
          rw [mem_insert, not_or]
          exact ⟨heq, hn'⟩
      . rw [update_update, ←h, update_same]
  . rintro (h | ⟨v', h, rfl⟩)
    . exact defined_on_mono (subset_insert _ _) h
    . apply defined_on_update h

theorem update_mem_models {s : Finset Nat} {v : Assignment} {i : Nat} (his : i ∈ s) (b : Bool)
      (h : v ∈ models s) :
    v.update i b ∈ models s := by
  rw [mem_models] at h |-
  intros j hj
  by_cases h' : j = i
  . cases h'; contradiction
  . rw [update_neg h']
    exact h hj

theorem InjOn_update {s : Finset Nat} {n : Nat} (h : n ∉ s) (b : Bool) :
    Set.InjOn (Assignment.update n b) (models s) := by
  intros v₁ v₁mem v₂ v₂mem heq
  ext n'
  by_cases h' : n' = n
  . cases h'
    simp only [Finset.mem_coe, mem_models] at v₁mem v₂mem
    rw [v₁mem h, v₂mem h]
  . rw [←v₁.update_neg h' b, ←v₂.update_neg h' b, heq]

@[simp] theorem card_models (s : Finset Nat) : card (models s) = 2 ^ card s := by
  induction s using Finset.induction; simp
  . next n s hns ih =>
    rw [models_insert, card_insert_of_not_mem hns, pow_succ, card_disjoint_union,
      card_image_of_injOn (InjOn_update hns true), ih, two_mul]
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    rw [mem_image] at hb
    rcases hb with ⟨b, _, rfl⟩
    rw [mem_models] at ha
    specialize ha hns
    rw [Assignment.update_pos rfl] at ha
    contradiction

theorem card_models_var {s : Finset Nat} {k : Nat} (hks : k ∈ s) :
    card ((models s).filter (λ v => v k)) = 2 ^ (card s - 1) := by
  have : ((models s).filter (λ v => v k)) =
    ((models (s.erase k)).image (update k true)) := by
      ext v
      rw [mem_filter, mem_image]
      constructor
      . intro ⟨vmem, vkeq⟩
        rw [mem_models] at vmem
        use  v.update k false
        constructor
        . rw [mem_models]
          intro i inmem
          by_cases hik : i = k
          . rw [update_pos hik]
          . rw [update_neg hik]
            rw [mem_erase, not_and] at inmem
            exact vmem (inmem hik)
        . rw [update_update, ←vkeq, update_same]
      . rintro ⟨v', v'mem, v'keq⟩
        constructor
        . rw [mem_models, ←v'keq]
          rw [mem_models] at v'mem
          intro i inmem
          have : i ≠ k := by rintro rfl; contradiction
          rw [update_neg this]
          apply v'mem
          rw [mem_erase, not_and_or]
          right
          exact inmem
        . rw [←v'keq, update_self]
  rw [this, card_image_of_injOn (InjOn_update (not_mem_erase k s) true), card_models,
    card_erase_of_mem hks]

/- auxiliary lemmas -/

theorem eval_update_eq_of_not_mem_vars {I : Iteg} {i : Fin I.val.size} {j : Nat}
      (h : j ∉ I.vars i) (v : Assignment) (b : Bool) :
    I.eval (v.update j b) i = I.eval v i := by
  rcases i with ⟨i, iLt⟩
  induction i using Nat.strongInductionOn with
    | ind i ih =>
      cases (I.val[i]'iLt).toEqCases
      . case eq_tr h' =>
        rw [I.eval_tr _ ⟨i, iLt⟩ h', I.eval_tr _ ⟨i, iLt⟩ h']
      . case eq_fls h' =>
        rw [I.eval_fls _ ⟨i, iLt⟩ h', I.eval_fls _ ⟨i, iLt⟩ h']
      . case eq_var k h' =>
        rw [I.eval_var _ ⟨i, iLt⟩ h', I.eval_var _ ⟨i, iLt⟩ h']
        rw [I.vars_var ⟨i, iLt⟩ h', mem_singleton] at h
        have : k ≠ j := by rintro rfl; contradiction   -- what happened to ne_symm?
        rw [update_neg this]
      . case eq_ite c t f h' =>
        -- have ⟨ht, hf⟩ := free_ite Ifree ⟨i, iLt⟩ h
        rw [I.eval_ite _ ⟨i, iLt⟩ h', I.eval_ite _ ⟨i, iLt⟩ h']
        rw [I.vars_ite ⟨i, iLt⟩ h', mem_insert, mem_union, not_or, not_or] at h
        rcases h with ⟨hc, ht, hf⟩
        have cne : c ≠ j := by rintro rfl; contradiction
        have tLt := (h' ▸ I.property ⟨i, iLt⟩).left
        have fLt := (h' ▸ I.property ⟨i, iLt⟩).right
        have iht := ih t tLt (tLt.trans iLt) ht
        have ihf := ih f fLt (fLt.trans iLt) hf
        rw [update_neg cne, iht, ihf]

theorem card_models_filter_of_not_mem {I : Iteg} {t : Fin I.val.size} {i : Nat} (his : i ∈ s)
      (h : ¬i ∈ vars I t) :
    card ((models s).filter (fun v => v i && I.eval v t)) =
      card ((models s).filter (fun v => !v i && I.eval v t)) := by
  let f := fun v : Assignment => v.update i false
  let S1 := (models s).filter (fun v => v i && I.eval v t)
  let S2 := (models s).filter (fun v => !v i && I.eval v t)
  have h1 : Set.InjOn f S1:= by
    simp only [Set.InjOn, Bool.and_eq_true, coe_filter, Set.mem_setOf_eq, and_imp]
    intros v1 _ v1eq _ v2 _ v2eq _ heq
    ext j
    by_cases h : j = i
    . rw [h, v1eq, v2eq]
    . have := congr_fun heq j
      rw [update_neg h, update_neg h] at this
      exact this
  have h2: S1.image f = S2 := by
    ext v
    simp only [Bool.and_eq_true, mem_image, mem_filter, Bool.not_eq_true']
    constructor
    . rintro ⟨v', ⟨⟨v'mem, _, evalv'eq⟩, rfl⟩⟩
      use update_mem_models his _ v'mem, update_self i false v'
      rw [eval_update_eq_of_not_mem_vars h, evalv'eq]
    . intro ⟨vmem, vieq, evalveq⟩
      use v.update i true
      constructor
      . use update_mem_models his _ vmem, update_self i true v
        rw [eval_update_eq_of_not_mem_vars h, evalveq]
      . ext j
        by_cases h : j = i
        . rw [update_pos h, h, vieq]
        . rw [update_neg h, update_neg h]
  rw [←congr_arg card h2, card_image_of_injOn h1]

theorem aux1 {I : Iteg} {t : Fin I.val.size} {s : Finset Nat} (hcs: c ∈ s) (hc : ¬c ∈ vars I t) :
      card ((models s).filter (fun v => I.eval v t)) =
    2 * card ((models s).filter (fun v => v c && I.eval v t)) := by
  have : (models s).filter (fun v => I.eval v t) =
    (models s).filter (fun v => v c && I.eval v t) ∪
      (models s).filter (fun v => !v c && I.eval v t) := by
    ext v; simp; cases v c <;> simp
  rw [this, card_disjoint_union, card_models_filter_of_not_mem hcs hc, two_mul]
  rw [disjoint_iff_ne]
  rintro v1 v1mem v2 v2mem rfl
  simp [mem_filter] at v1mem v2mem; cases (v1 c) <;> simp_all

theorem aux2 {I : Iteg} {f : Fin I.val.size} {s : Finset Nat} (hcs : c ∈ s) (hc : ¬c ∈ vars I f) :
  card ((models s).filter (fun v => I.eval v f)) =
    2 * card ((models s).filter (fun v => !v c && I.eval v f)) := by
  rw [←card_models_filter_of_not_mem hcs hc, aux1 hcs hc]

theorem card_models_ite {I : Iteg} {t f : Fin I.val.size} {s : Finset Nat} {c : Nat}
    (h₀ : c ∈ s) (h₁ : c ∉ I.vars t) (h₂ : c ∉ I.vars f) :
  card ((models s).filter (λ v => cond (v c) (eval I v t) (eval I v f))) =
    (card ((models s).filter (λ v => eval I v t)) +
      card ((models s).filter (λ v => eval I v f))) / 2 := by
  apply Eq.symm
  apply Nat.div_eq_of_eq_mul_right; exact Nat.zero_lt_succ _
  have : ((models s).filter (λ v => cond (v c) (eval I v t) (eval I v f))) =
      (((models s).filter (λ v => v c && (eval I v t))) ∪
       ((models s).filter (λ v => !(v c) &&(eval I v f)))) := by
    ext v
    simp [mem_filter]; cases (v c) <;> simp
  rw [this, card_disjoint_union, Nat.mul_add, aux1 h₀ h₁, aux2 h₀ h₂]
  rw [disjoint_iff_ne]
  rintro v1 v1mem v2 v2mem rfl
  simp [mem_filter] at v1mem v2mem; cases (v1 c) <;> simp_all

/- the main theorem -/

theorem card_models_Iteg (I : Iteg) (Ifree : free I) (s : Finset Nat) :
    ∀ i, I.vars i ⊆ s → card ((models s).filter (λ v => I.eval v i)) = I.count (card s) i := by
  intro ⟨i, iLt⟩
  induction i using Nat.strongInductionOn with
    | ind i ih =>
      intro hvars
      cases (I.val[i]'iLt).toEqCases
      . case eq_tr h =>
        rw [I.count_tr (card s) ⟨i, iLt⟩ h, ←card_models]
        congr
        apply Eq.trans _ (filter_true)
        congr; ext v
        rw [I.eval_tr v ⟨i, iLt⟩ h]
      . case eq_fls h =>
        rw [I.count_fls (card s) ⟨i, iLt⟩ h, ←card_empty]
        congr
        apply Eq.trans _ (filter_false (models s))
        congr; ext v
        rw [I.eval_fls v ⟨i, iLt⟩ h]
      . case eq_var k h =>
        rw [I.vars_var ⟨i, iLt⟩ h] at hvars
        rw [I.count_var (card s) ⟨i, iLt⟩ h, ←card_models_var (hvars (mem_singleton_self _))]
        congr; ext v
        rw [I.eval_var v ⟨i, iLt⟩ h]
      . case eq_ite c t f h =>
        have ⟨ht, hf⟩ := free_ite Ifree ⟨i, iLt⟩ h
        rw [I.count_ite (card s) ⟨i, iLt⟩ h]
        rw [I.vars_ite ⟨i, iLt⟩ h] at hvars
        apply Eq.trans _ (Eq.trans (card_models_ite (hvars (mem_insert_self _ _)) ht hf) _)
        . congr; ext v
          rw [I.eval_ite v ⟨i, iLt⟩ h]
        . have tLt := (h ▸ I.property ⟨i, iLt⟩).left
          have fLt := (h ▸ I.property ⟨i, iLt⟩).right
          have iht := ih t tLt (tLt.trans iLt) <|
            subset_union_left _ _ |>.trans (subset_insert _ _) |>.trans hvars
          have ihf := ih f fLt (fLt.trans iLt) <|
            subset_union_right _ _ |>.trans (subset_insert _ _) |>.trans hvars
          rw [iht, ihf]

def countModelsAux (I : Iteg) (numVars : Nat) :
      (n : Nat) → (A : Array Nat) → (I.val.size = A.size + n) →
    { A : Array Nat // A.size = I.val.size }
  | 0, A, h => by
    use A
    exact h.symm
  | n + 1, A, h  =>
    have AsizeLt : A.size < I.val.size := by
      rw [h, ←add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    let nextElt :=
      match I.val[A.size]'AsizeLt, I.property ⟨A.size, AsizeLt⟩ with
        | tr,               _        => 2^numVars
        | fls,              _        => 0
        | var k,            _        => 2^(numVars - 1)
        | IteElt.ite _ t f, ⟨ht, hf⟩ => (A[t] + A[f])/2
    let nextA := A.push nextElt
    have next_h : I.val.size = nextA.size + n := by
      rw [h, Array.size_push, add_assoc, add_comm n]
    countModelsAux I numVars n nextA next_h

theorem countModelsAux_correct (I : Iteg) (numVars : Nat) :
      (n : Nat) → (A : Array Nat) → (h : I.val.size = A.size + n) →
      (h' : ∀ i : Fin A.size, ∀ i' : Fin I.val.size, i.val = i'.val → A[i] = I.count numVars i') →
    ∀ i : Fin (countModelsAux I numVars n A h).val.size, ∀ i' : Fin I.val.size,
      i.val = i'.val → (countModelsAux I numVars n A h).val[i] = I.count numVars i'
  | 0,     _, _, h' => h'
  | n + 1, A, h, h' => by
    have AsizeLt : A.size < I.val.size := by
      rw [h, ←add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    let nextElt :=
      match I.val[A.size]'AsizeLt, I.property ⟨A.size, AsizeLt⟩ with
        | tr,               _        => 2^numVars
        | fls,              _        => 0
        | var k,            _        => 2^(numVars - 1)
        | IteElt.ite _ t f, ⟨ht, hf⟩ => (A[t] + A[f])/2
    let nextA := A.push nextElt
    have next_h : I.val.size = nextA.size + n := by
      rw [h, Array.size_push, add_assoc, add_comm n]
    apply countModelsAux_correct I numVars n nextA next_h
    intro ⟨i, iLt⟩ i' heq
    cases heq
    rw [Array.size_push] at iLt
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ iLt) with hlt | heq
    . show (Array.push _ _)[_] = _
      apply Eq.trans
      apply Array.get_push_lt _ _ _ hlt
      apply h' ⟨i'.1, hlt⟩ i'
      rfl
    . show (Array.push _ _)[_] = _
      apply Eq.trans
      apply Array.get_push
      rw [dif_neg]; swap; simp [heq]
      have AsizeLt : A.size < I.val.size := heq ▸ i'.2
      have i'eq : i' = ⟨Array.size A, AsizeLt⟩ := by ext; exact heq
      rw [i'eq]
      cases (I.val[Array.size A]'AsizeLt).toEqCases
      . case eq_tr h'' =>
        rw [I.count_tr _ ⟨Array.size A, AsizeLt⟩ h'']
        revert nextElt; dsimp; split <;> simp_all
      . case eq_fls h'' =>
        rw [I.count_fls _ ⟨Array.size A, AsizeLt⟩ h'']
        revert nextElt; dsimp; split <;> simp_all
      . case eq_var k h'' =>
        rw [I.count_var _ ⟨Array.size A, AsizeLt⟩ h'']
        revert nextElt; dsimp; split <;> simp_all
      . case eq_ite c t f h'' =>
        rw [I.count_ite _ ⟨Array.size A, AsizeLt⟩ h'']
        revert nextElt; dsimp; split <;> simp_all
        next c' t' f' ht' hf' _ _ _ =>
        . intro _
          rw [h' ⟨t', ht'⟩ ⟨t', ht'.trans AsizeLt⟩]
          rw [h' ⟨f', hf'⟩ ⟨f', hf'.trans AsizeLt⟩]
          rfl
          rfl

def countModels (I : Iteg) (numVars : Nat) : { A : Array Nat // A.size = I.val.size } :=
  countModelsAux I numVars I.val.size #[] (zero_add _).symm

theorem countModels_correct (I : Iteg) (freeI : free I) (i : Fin I.val.size) :
    let A := countModels I (card (I.vars i))
    let i' : Fin (A.val.size) := ⟨i, by rw [A.property]; exact i.2⟩
    A.val[i'] = card ((models (I.vars i)).filter (λ v => I.eval v i)) := by
  let A := countModels I (card (I.vars i))
  let i' : Fin (A.val.size) := ⟨i, by rw [A.property]; exact i.2⟩
  have := countModelsAux_correct I (card (I.vars i)) I.val.size #[] (zero_add _).symm
    (by intro ⟨i, ilt⟩; simp at ilt) i' i rfl
  apply Eq.trans this
  exact card_models_Iteg I freeI _ _ (subset_refl _) |>.symm
