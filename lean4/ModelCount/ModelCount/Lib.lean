import Mathlib.Data.Nat.Basic
import Mathlib.Set
import Mathlib.Data.List.Card

namespace Classical

theorem not_and {p q : Prop} : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := by
  cases (Decidable.em p) with
  | inl h => simp [h]
  | inr h => simp [h]

theorem dne {p : Prop} : ¬ ¬ p ↔ p := by
  cases (Decidable.em p) with
  | inl h => simp [h]
  | inr h => simp [h]

end Classical


namespace Nat

theorem lt_succ_iff_le {a b : Nat} : a < b + 1 ↔ a ≤ b :=
  ⟨le_of_lt_succ, lt_succ_of_le⟩

theorem le_iff_lt_or_eq {a b : Nat} : a ≤ b ↔ a < b ∨ a = b := by
  split
    intro h; rw [or_comm]; apply Nat.eq_or_lt_of_le h
  intro h
  cases h with
  | inl h => exact Nat.le_of_lt h
  | inr h => rw [h]; apply Nat.le_refl

theorem CompleteInductionOn
    {motive : Nat → Prop}
    (x : Nat)
    (ind : ∀ x, (∀ y, y < x → motive y) → motive x) :
  motive x :=
have : ∀ z, ∀ y, y < z → motive y := by
  intro z
  induction z with
  | zero      =>
      intros _ h
      exact False.elim (Nat.not_lt_zero _ h)
  | succ x ih =>
      intros y ylt
      cases (le_iff_lt_or_eq.mp (lt_succ_iff_le.mp ylt)) with
      | inl h1 => exact ih _ h1
      | inr h1 => rw [h1]
                  exact ind _ ih
this _ x (Nat.lt_succ_self _)

theorem mul_two (x : Nat) : x * 2 = x + x := by
  have : (1 : Nat) + 1 = 2 := rfl
  rw [←this, Nat.mul_add, Nat.mul_one]

theorem two_mul (x : Nat) : 2 * x = x + x := by rw [Nat.mul_comm, mul_two]

end Nat


@[simp] theorem cond_true (t f : α) : cond true t f = t := rfl

@[simp] theorem cond_false (t f : α) : cond false t f = f := rfl

namespace Bool

@[simp] theorem not_false : (!false) = true := rfl

@[simp] theorem not_true : (!true) = false := rfl

theorem eq_true_or_eq_false (b : Bool) : b = true ∨ b = false := by cases b <;> simp

end Bool

namespace List

theorem subset_trans {as bs cs : List α} (h₁ : as ⊆ bs) (h₂ : bs ⊆ cs) : as ⊆ cs :=
λ h => h₂ (h₁ h)

theorem subset_union_left [DecidableEq α] (as bs : List α) : as ⊆ as.union bs :=
fun hx => mem_union_iff.mpr (Or.inl hx)

theorem subset_union_right [DecidableEq α] (as bs : List α) : bs ⊆ as.union bs :=
fun hx => mem_union_iff.mpr (Or.inr hx)

theorem subset_insert [DecidableEq α] (a : α) (as : List α) : as ⊆ insert a as :=
λ hx => mem_insert_iff.mpr (Or.inr hx)

section
variable (a : α) (as bs cs : List α)

theorem reverse_def : reverse as = reverseAux as [] := rfl

theorem reverseAux_nil : reverseAux [] as = as := rfl

theorem reverseAux_cons : reverseAux (a :: as) bs = reverseAux as (a :: bs) := rfl

theorem reverse_nil : reverse ([] : List α) = [] := rfl
theorem reverseAux_append : reverseAux (as ++ bs) cs = reverseAux bs (reverseAux as cs) := by
  induction as generalizing cs with
  | nil => rw [nil_append, reverseAux_nil]
  | cons a as ih => rw [cons_append, reverseAux_cons, reverseAux_cons, ih]

theorem reverseAux_append' : reverseAux as (bs ++ cs) = reverseAux as bs ++ cs := by
  induction as generalizing bs with
  | nil => rw [reverseAux_nil, reverseAux_nil]
  | cons a as ih => rw [reverseAux_cons, reverseAux_cons, ←cons_append, ih]

theorem reverse_append : reverse (as ++ bs) = reverse bs ++ reverse as := by
  rw [reverse_def, reverseAux_append, reverse_def, ←reverseAux_append', nil_append, reverse_def]

theorem cons_eq_append : a :: as = [a] ++ as := by rw [cons_append, nil_append]

theorem reverse_cons : reverse (a :: as) = reverse as ++ [a] := by
  rw [cons_eq_append, reverse_append]; rfl

end

def filter' (p : α → Bool) : List α → List α
  | [] => []
  | (a :: as) => cond (p a) (a :: filter' p as) (filter' p as)

theorem filter'_eq_filter (p : α → Bool) (as : List α) : filter' p as = filter p as := by
  simp [filter]; rw [aux]; rfl
where
  aux (p : α → Bool) (as bs : List α) : filterAux p as bs = reverse bs ++ filter' p as := by
    induction as generalizing bs with
      | nil => simp [filterAux, filter']
      | cons a as ih =>
        simp [filterAux, filter']
        cases p a with
          | true => simp [ih]; rw [reverse_cons, cons_eq_append a (filter' p as), append_assoc]
          | false => simp [ih]

@[simp] theorem filter_nil (p : α → Bool) : filter p [] = [] := rfl

theorem filter_cons (p : α → Bool) (a : α) (as : List α) :
    filter p (a :: as) = cond (p a) (a :: filter p as) (filter p as) := by
  rw [←filter'_eq_filter]; rw [←filter'_eq_filter]; rfl

@[simp] theorem filter_true (as : List α) : as.filter (fun x => true) = as := by
  induction as with
  | nil => rw [filter_nil]
  | cons a as ih => rw [filter_cons, cond_true, ih]

@[simp] theorem filter_false (as : List α) : as.filter (fun x => false) = ∅ := by
  induction as with
  | nil => rw [filter_nil]; rfl
  | cons a as ih => rw [filter_cons, cond_false, ih]

theorem not_mem_remove [DecidableEq α] (a : α) (as : List α) :
  a ∉ remove a as := by simp [mem_remove_iff]

theorem card_remove_of_mem' [DecidableEq α] {as : List α} (h : a ∈ as) :
    card (remove a as) = card as - 1 := by rw [card_remove_of_mem h, Nat.add_sub_cancel]

end List


namespace Array

@[simp] theorem size_empty : Array.size (#[] : Array α) = 0 := rfl

theorem get_push_of_lt [Inhabited α] (A : Array α) (x : α) {i : Nat} (h : i < A.size) :
  (A.push x)[i] = A[i] := by
  have h' : i < A.data.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
  simp [getOp, get!, push, getD, h', h, get]
  apply get_push_of_lt_aux
where
  get_push_of_lt_aux : ∀ (as : List α) (a : α) (i : Nat) (h : i < as.length)
      (h' : i < (as.concat a).length),
    List.get (as.concat a) i h' = List.get as i h
  | [], a, i => (fun h h' => absurd h (Nat.not_lt_zero _))
  | (b :: bs), a, 0 => by simp [List.get, List.concat, List.length_concat]
  | (b :: bs), a, (Nat.succ i) => by
    simp [List.get, List.concat, List.length_concat]
    intro h h'
    simp [List.get]
    apply get_push_of_lt_aux

@[simp] theorem get_push_size [Inhabited α] (A : Array α) (x : α) :
    (A.push x)[A.size] = x := by
  have h : List.length A.data < List.length A.data + 1 := Nat.lt_succ_self _
  simp [getOp, get!, push, getD, size, get, h, get_push_size_aux]
where
  get_push_size_aux : ∀ (as : List α) (a : α) (h : as.length < (as.concat a).length),
    List.get (as.concat a) (as.length) h = a
  | [], a => by intro h; simp [List.get]
  | (b :: bs), a => by
    simp [List.get, List.concat, List.length_concat]
    rw [List.length_cons]
    intro h
    simp [List.get]
    apply get_push_size_aux

end Array


/- From Mario -/

namespace Lean.Elab.Tactic
open Meta

syntax (name := trustme) "trustme" term : tactic
@[tactic «trustme»] def evalTrustme : Tactic := fun stx =>
  match stx with
  | `(tactic| trustme $e) => closeMainGoalUsing (fun type => elabTerm e type)
  | _                   => throwUnsupportedSyntax

end Lean.Elab.Tactic

namespace Std.Range.forIn

theorem loop_eq {β : Type u} {m : Type u → Type v} [Monad m]
  (range : Std.Range) (f : Nat → β → m (ForInStep β)) (i j : Nat) (b : β) :
  loop range f i j b =
  Nat.brecOn (motive := fun _ => Nat → β → m β) i
    (fun i (F : Nat.below i) (j : Nat) (b : β) =>
      if j ≥ range.stop then pure b else
        (match i : ∀ i, Nat.below i → m β with
          | 0 => fun x => pure b
          | Nat.succ i => fun x =>
            do match ← f j b with
            | ForInStep.done b => pure b
            | ForInStep.yield b => by exact PProd.fst x.fst (j + range.step) b)
          F)
    j b := by
  trustme (rfl : loop range f i j b = _)

@[simp] theorem loop_zero {β : Type u} {m : Type u → Type v} [Monad m]
  (range : Std.Range) (f : Nat → β → m (ForInStep β)) (j : Nat) (b : β) :
  loop range f 0 j b = pure b := by
  simp [loop_eq]
  show (if range.stop ≤ j then pure b else pure b : m β) = pure b
  cases Nat.decLe range.stop j <;> rfl

@[simp] theorem loop_succ {β : Type u} {m : Type u → Type v} [Monad m]
  (range : Std.Range) (f : Nat → β → m (ForInStep β)) (i j : Nat) (b : β) :
  loop range f (Nat.succ i) j b =
  (if j ≥ range.stop then pure b else do
    match ← f j b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => loop range f i (j + range.step) b) := by
  simp [loop_eq]

theorem loop_stop {β : Type u} {m : Type u → Type v} [Monad m]
  (range : Std.Range) (f : Nat → β → m (ForInStep β)) (i j : Nat) (b : β)
  (h : range.stop ≤ j) : loop range f i j b = pure b := by
  cases i <;> simp [h]

theorem loop_non_stop {β : Type u} {m : Type u → Type v} [Monad m]
  (range : Std.Range) (f : Nat → β → m (ForInStep β)) (i j : Nat) (b : β)
  (h : ¬ range.stop ≤ j) : loop range f (Nat.succ i) j b = (do
    match ← f j b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => loop range f i (j + range.step) b) := by
  simp [h]

end Std.Range.forIn
