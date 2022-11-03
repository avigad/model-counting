import Mathlib.Init.Set

/-- A propositional formula over variables of type `ν`. -/
inductive PropForm (ν : Type)
  | var (x : ν)
  | tr
  | fls
  | neg (φ : PropForm ν)
  | conj (φ₁ φ₂ : PropForm ν)
  | disj (φ₁ φ₂ : PropForm ν)
  | impl (φ₁ φ₂ : PropForm ν)
  | biImpl (φ₁ φ₂ : PropForm ν)
  deriving Repr, DecidableEq, Inhabited

namespace PropForm

/-- Variables appearing in the formula. Sometimes called its "support set". -/
def vars (φ : PropForm ν) : Set ν :=
  fun x => match φ with
  | var y => x = y
  | tr | fls => false
  | neg φ => x ∈ vars φ
  | conj φ₁ φ₂ | disj φ₁ φ₂ | impl φ₁ φ₂ | biImpl φ₁ φ₂ => x ∈ vars φ₁ ∨ x ∈ vars φ₂

end PropForm

/-- A total assignment of truth values to variables. -/
def PropAssignment ν := ν → Bool

/-- The typeclass for semantic entailment notation `⊨`. -/
class SemanticEntails (α : Type u) (β : outParam $ Type v) where
  entails : α → β → Prop

infix:51 " ⊨ " => SemanticEntails.entails
infix:51 " ⊭ " => fun φ ψ => ¬(φ ⊨ ψ)

namespace PropAssignment
open PropForm

def eval (τ : PropAssignment ν) : PropForm ν → Bool
  | var x => τ x
  | tr => true
  | fls => false
  | neg φ => !(eval τ φ)
  | conj φ₁ φ₂ => (eval τ φ₁) && (eval τ φ₂)
  | disj φ₁ φ₂ => (eval τ φ₁) || (eval τ φ₂)
  | impl φ₁ φ₂ => !(eval τ φ₁) || (eval τ φ₂)
  | biImpl φ₁ φ₂ => τ.eval φ₁ = τ.eval φ₂

/-- An assignment satisfies a formula φ when φ evaluates to true at that assignment. -/
def satisfies (τ : PropAssignment ν) (φ : PropForm ν) : Prop :=
  τ.eval φ = true

instance {ν : Type} : SemanticEntails (PropAssignment ν) (PropForm ν) where
  entails := satisfies

def satisfiable (φ : PropForm ν) : Prop :=
  ∃ τ : PropAssignment ν, τ ⊨ φ

def valid (φ : PropForm ν) : Prop :=
  ∀ τ : PropAssignment ν, τ ⊨ φ

theorem satisfies_var {τ : PropAssignment ν} {x : ν} : τ ⊨ var x ↔ τ x :=
  by simp [SemanticEntails.entails, satisfies, eval]

theorem satisfies_tr {τ : PropAssignment ν} : τ ⊨ tr :=
  by simp [SemanticEntails.entails, satisfies, eval]

theorem not_satisfies_fls {τ : PropAssignment ν} : τ ⊭ fls :=
  fun h => nomatch h

@[simp] theorem Bool.bnot_eq_to_not_eq (a b : Bool) :
  ((!a) = b) = ¬(a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_bnot_to_not_eq (a b : Bool) :
  (a = (!b)) = ¬(a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_true_iff_eq_true_to_eq (a b : Bool) :
  (a = true ↔ b = true) = (a = b) := by cases a <;> cases b <;> decide
@[simp] theorem Bool.eq_false_iff_eq_false_to_eq (a b : Bool) :
  (a = false ↔ b = false) = (a = b) := by cases a <;> cases b <;> decide

theorem satisfies_neg {τ : PropAssignment ν} {φ : PropForm ν} : τ ⊨ neg φ ↔ τ ⊭ φ :=
  by simp [SemanticEntails.entails, satisfies, eval]

theorem satisfies_conj {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ conj φ₁ φ₂ ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ :=
  by simp [SemanticEntails.entails, satisfies, eval]

theorem satisfies_disj {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .disj φ₁ φ₂ ↔ τ ⊨ φ₁ ∨ τ ⊨ φ₂ :=
  by simp [SemanticEntails.entails, satisfies, eval]

theorem satisfies_impl {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .impl φ₁ φ₂ ↔ τ ⊭ φ₁ ∨ τ ⊨ φ₂ :=
  by simp [SemanticEntails.entails, satisfies, eval]

theorem satisfies_biImpl {τ : PropAssignment ν} {φ₁ φ₂ : PropForm ν} : τ ⊨ .biImpl φ₁ φ₂ ↔ (τ ⊨ φ₁ ↔ τ ⊨ φ₂) :=
  by simp [SemanticEntails.entails, satisfies, eval]

end PropAssignment

namespace PropForm

open scoped PropAssignment

def entails (φ₁ φ₂ : PropForm ν) : Prop :=
  ∀ (τ : PropAssignment ν), τ ⊨ φ₁ → τ ⊨ φ₂

instance : SemanticEntails (PropForm ν) (PropForm ν) where
  entails := entails

def equivalent (φ₁ φ₂ : PropForm ν) : Prop :=
  φ₁ ⊨ φ₂ ∧ φ₂ ⊨ φ₁

infix:51 " ≡ " => PropForm.equivalent

end PropForm
