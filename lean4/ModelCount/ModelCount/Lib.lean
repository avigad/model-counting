import Init
import Lean.Elab.Tactic

/- Facts about Nat -/

namespace Nat

theorem le_refl (a : Nat) : a ≤ a := sorry
theorem le_trans {a b c : Nat} : a ≤ b → b ≤ c → a ≤ c := sorry
theorem lt_trans {a b c : Nat} : a < b → b < c → a < c := sorry
theorem le_of_lt {a b : Nat} : a < b → a ≤ b := sorry
theorem not_le_of_lt {a b : Nat} : a < b → ¬ b ≤ a := sorry
theorem le_of_not_le {a b : Nat} : ¬ a ≤ b → b ≤ a := sorry
theorem lt_or_eq {a b : Nat} : a ≤ b → a < b ∨ a = b := sorry
theorem lt_succ_of_lt {a b : Nat} : a < b → a < b + 1 := sorry
theorem not_lt_zero (a : Nat) : ¬ a < 0 := sorry
theorem lt_of_lt_of_le {a b c : Nat} : a < b → b ≤ c → a < c := sorry
theorem lt_succ_iff_le {a b : Nat} : a < b + 1 ↔ a ≤ b:= sorry
theorem lt_succ_self (a : Nat) : a < a + 1 := lt_succ_iff_le.mpr (le_refl a)
theorem le_iff_lt_or_eq {a b : Nat} : a ≤ b ↔ a < b ∨ a = b := sorry
theorem le_add_right (a b : Nat) : a ≤ a + b  := sorry 

theorem CompleteInductionOn
    {motive : Nat → Prop}
    (x : Nat)
    (ind : ∀ x, (∀ y, y < x → motive y) → motive x) :
  motive x :=
have ∀ z, ∀ y, y < z → motive y by
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

end Nat

/- Sets and finite sets -/

def Set (α : Type) := α → Prop

namespace Set

def mem (a : α) (s : Set α) := s a
def empty {α : Type} : Set α := fun a => False
def singleton (a : α) := fun b => b = a
def union (s t : Set α) := fun a => mem a s ∨ mem a t
def sep (s : Set α) (P : α → Prop) := fun a => mem a s ∧ P a
def univ {α : Type} : Set α := fun a => True
def subset (s t : Set α) : Prop := ∀ {x}, mem x s → mem x t

scoped infix:65 " ⊆ " => subset

theorem ext {s t : Set α} (h : ∀ x, mem x s ↔ mem x t) : s = t := funext (fun x => propext (h x))

theorem sep_subset (s : Set α) (P : α → Prop) : sep s P ⊆ s :=
fun ⟨xs, Px⟩ => xs

inductive finite : Set α → Prop where
  | empty : finite empty
  | singleton : finite (singleton a)
  | union {s t : Set α} : finite s → finite t → finite (union s t)
  | subset {s t : Set α} : finite t → subset s t → finite s

theorem finite.sep {s : Set α} (finS : finite s) (P : α → Prop) : finite (sep s P) :=
  finite.subset finS (sep_subset s P)

end Set

namespace Subtype

theorem ext {P : α → Prop} : ∀ {a1 a2 : {x // P x}}, a1.val = a2.val → a1 = a2
  | ⟨x1, h1⟩, ⟨x2, h2⟩, h => by cases h; rfl

end Subtype

def Finset α := { s : Set α // Set.finite s }

namespace Finset 

def mem (a : α) (s : Finset α) := s.1 a
def empty {α : Type} : Finset α := ⟨Set.empty, Set.finite.empty⟩
def singleton (a : α) : Finset α := ⟨Set.singleton a, Set.finite.singleton⟩
def union (s t : Finset α) : Finset α := ⟨Set.union s.1 t.1, Set.finite.union s.2 t.2⟩
def sep (s : Finset α) (P : α → Prop) : Finset α := ⟨Set.sep s.1 P, Set.finite.sep s.2 _⟩
def subset (s t : Finset α) : Prop := ∀ {x}, mem x s → mem x t

scoped infix:50 " ∈ " => mem

scoped notation "∅" => empty
scoped infixr:65 " ∪ " => union
scoped infixl:50 " ⊆ " => subset

syntax:50 term " ∉ " term:49 : term
macro_rules | `($x ∉ $y) => `((¬ ($x ∈ $y)))

scoped macro "{" x:ident " ∈ " s:term "|" p:term "}" : term => `(sep $s (fun $x => $p))
scoped macro "{" x:ident " : " t:term " ∈ " s:term "|" p:term "}" : term => 
  `(sep s (fun ($x : $t) => $p))

def disjoint (s t : Finset α) := ∀ a, ¬ (a ∈ s ∧ a ∈ t)

theorem ext {s t : Finset α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := Subtype.ext $ Set.ext h

--funext (fun x => propext (h x))
@[simp] theorem mem_empty (a : α) : a ∈ ∅ ↔ False := Iff.refl _
@[simp] theorem mem_singleton {a b : α} : a ∈ singleton b ↔ a = b := Iff.refl _
@[simp] theorem mem_union {a : α} {s t : Finset α} : a ∈ union s t ↔ a ∈ s ∨ a ∈ t := Iff.refl _

@[simp] theorem sep_True (s : Finset α) : { x ∈ s | True } = s := 
  ext $ fun x => ⟨fun h => h.1, fun h => ⟨h, True.intro⟩⟩ 

@[simp] theorem sep_False (s : Finset α) : { x ∈ s | False } = (∅ : Finset α) := 
  ext $ fun x => ⟨fun h => h.2, fun h => ⟨False.elim h, h⟩⟩

theorem subset_def (s t : Finset α) : s ⊆ t ↔ (∀ x, x ∈ s → x ∈ t) := Iff.refl _

theorem subset_trans {s t u : Finset α} (h₀ : s ⊆ t) (h₁ : t ⊆ u) : s ⊆ u :=
fun hx => h₁ (h₀ hx)

@[simp] theorem singleton_subset {a : α} {s : Finset α} : singleton a ⊆ s ↔ a ∈ s := by
  simp [subset_def]
  apply Iff.intro
  { intro h; apply h; rfl }
  { intros h x xeq; rw [xeq]; exact h }

theorem subset_union_left  (s t : Finset α) : s ⊆ s ∪ t := by { intros x hx; exact Or.inl hx }
theorem subset_union_right (s t : Finset α) : t ⊆ s ∪ t := by { intros x hx; exact Or.inr hx }
 
/- axiomatize cardinality for now -/
axiom card {α : Type} : Finset α → Nat

@[simp] theorem card_empty {α : Type} : card (empty : Finset α) = 0 := sorry
@[simp] theorem card_singleton {α : Type} (a : α) : card (singleton a) = 1 := sorry
@[simp] theorem card_union {α : Type} {s t : Finset α} (h : disjoint s t) : 
  card (s ∪ t) = card s + card t := sorry

end Finset

namespace Array

@[simp] theorem size_empty : Array.size (#[] : Array α) = 0 := rfl

theorem get_push_of_lt [Inhabited α] (A : Array α) (x : α) {i : Nat} (h : i < A.size) :
  (A.push x)[i] = A[i] :=
sorry

@[simp] theorem get_push_size [Inhabited α] (A : Array α) (x : α) :
  (A.push x)[A.size] = x :=
sorry

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
