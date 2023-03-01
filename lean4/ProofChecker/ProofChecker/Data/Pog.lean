import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import ProofChecker.Data.ICnf
import ProofChecker.CountModels

abbrev Var := Nat

/-
The current implementation assumes that nodes are added consecutively, without gaps, and throws an
exception otherwise. This enables us to maintain the invariant that the variable or extension
variable corresponding to the entry at index `n` is `n + 1`.

We nonetheless store the name anyhow, to make it easier to loosen that requirement in the future.
We can do that straightforwardly by adding a hashmap that maps each variable to the corresponding
index.
-/

inductive PogElt where
  | var  : Var → PogElt
  | disj : Var → ILit → ILit → PogElt
  | conj : Var → Array ILit → PogElt
deriving Repr, DecidableEq, Inhabited

namespace PogElt

inductive PogEqCases (pogElt : PogElt): Prop where
  | eq_var  (n : Var)                     : pogElt = var n → PogEqCases pogElt
  | eq_disj (n : Var) (left right : ILit) : pogElt = disj n left right → PogEqCases pogElt
  | eq_conj (n : Var) (args : Array ILit) : pogElt = conj n args → PogEqCases pogElt

open PogEqCases in
theorem toEqCases (pogElt : PogElt) : PogEqCases pogElt := by
  cases pogElt
  . case var n => exact eq_var n rfl
  . case disj n left right => exact eq_disj n left right rfl
  . case conj n args => exact eq_conj n args rfl

def varNum : PogElt → Var
  | var n      => n
  | disj n _ _ => n
  | conj n _   => n

-- If we generalize to let variables come in any order, we need only change this to add the indexing
-- function and require `index left.var < index n`, etc.

def decreasing : PogElt → Prop
  | var _             => true
  | disj n left right => left.var < n ∧ right.var < n
  | conj n args       =>  ∀ i : Fin args.size, args[i].var < n

end PogElt

structure Pog :=
  (elts : Array PogElt)
  (wf : ∀ i : Fin elts.size, elts[i].decreasing)
  (inv : ∀ i : Fin elts.size, elts[i].varNum = i + 1)

def PogError := String

namespace Pog
open PogElt

def empty : Pog where
  elts := #[]
  wf := fun i => i.elim0
  inv := fun i => i.elim0

def push (pogElt : PogElt) (pog : Pog)
    (hwf : decreasing pogElt) (hinv : pogElt.varNum = pog.elts.size + 1) : Pog where
  elts := pog.elts.push pogElt
  wf := by
    intro ⟨i, h'⟩
    rw [Array.size_push] at h'
    cases (lt_or_eq_of_le (Nat.le_of_lt_succ h'))
    . case inl h' =>
      dsimp
      rw [Array.get_push_lt _ _ _ h']
      apply pog.wf ⟨i, h'⟩
    . case inr h' =>
      dsimp
      cases h'
      rw [Array.get_push_eq]
      exact hwf
  inv := by
      intro ⟨i, h'⟩
      rw [Array.size_push] at h'
      cases (lt_or_eq_of_le (Nat.le_of_lt_succ h'))
      . case inl h' =>
        dsimp
        rw [Array.get_push_lt _ _ _ h']
        apply pog.inv ⟨i, h'⟩
      . case inr h' =>
        cases h'
        dsimp
        rw [Array.get_push_eq, hinv]

def addVar (x : Var) (pog : Pog) : Except PogError Pog :=
  if h : x = pog.elts.size + 1 then
    .ok <| pog.push (var x) (by trivial) h
  else
    .error s!"Pog variable {x} added, {pog.elts.size + 1} expected"

def addDisj (x : Var) (left right : ILit) (pog : Pog) : Except PogError Pog :=
  if h : x = pog.elts.size + 1 then
    if hleft : left.var < x then
      if hright : right.var < x then
        .ok <| pog.push (disj x left right) ⟨hleft, hright⟩ h
      else
        .error "Pog disjunction {n} added, right argument {right} missing"
    else
      .error <| "Pog disjunction {n} added, left argument {left} missing"
  else
    .error "Pog disjunction {n} added, {pog.elts.size + 1} expected"

def addConj (x : Var) (args : Array ILit) (pog : Pog) : Except PogError Pog :=
  if h : x = pog.elts.size + 1 then
    if hargs : ∀ i : Fin args.size, args[i].var < x then
      .ok <| pog.push (conj x args) hargs h
    else
      .error "Pog conjunction {n} added, argument missing"
  else
    .error "Pog conjunction {n} added, {pog.elts.size + 1} expected"

def toPropForm (l : ILit) : Pog → PropForm Var := sorry

theorem toPropForm_neg (x : Var) (p : Pog) :
    p.toPropForm (.mkNeg x) = .neg (p.toPropForm (.mkPos x)) := sorry

theorem toPropForm_addVar (x : Var) (p p' : Pog) :
    p.addVar x = .ok p' →
    p'.toPropForm (.mkPos x) = .var x := sorry

theorem toPropForm_addVar_of_ne (x y : Var) (p p' : Pog) :
    p.addVar x = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y) := sorry

theorem toPropForm_addDisj (x : Var) (l₁ l₂ : ILit) (p p' : Pog) :
    p.addDisj x l₁ l₂ = .ok p' →
    p'.toPropForm (.mkPos x) = .disj (p.toPropForm l₁) (p.toPropForm l₂) := sorry

theorem toPropForm_addDisj_of_ne (x y : Var) (l₁ l₂ : ILit) (p p' : Pog) :
    p.addDisj x l₁ l₂ = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y) := sorry

theorem toPropForm_addConj (x : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' →
    p'.toPropForm (.mkPos x) =
      -- NOTE: This could change, and the `.tr` part is awkward. Should we have one canonical way
      -- to structurally turn a cube into a PropForm?
      ls.foldl (init := .tr) (fun acc l => acc.conj (p.toPropForm l)) := sorry

theorem toPropForm_addConj_of_ne (x y : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y) := sorry

/-
The count function
-/

def count (x : Var) (nVars : Nat) : Pog → Nat := fun _ => 0

axiom count_of_decomposable (x : Var) (φ : PropForm Var) (p : Pog) (nVars : Nat) :
    p.toPropForm (.mkPos x) = φ → φ.decomposable →
    p.count x nVars = φ.countModels nVars

end Pog