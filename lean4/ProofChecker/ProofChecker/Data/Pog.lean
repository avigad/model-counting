import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.PNat.Basic
import ProofChecker.Data.ICnf
import ProofChecker.CountModels

open Nat

/-
The current implementation assumes that nodes are added consecutively, without gaps, and throws an
exception otherwise. This enables us to maintain the invariant that the variable (possibly an
extension variable) corresponding to the entry at index `n` is `n + 1`.

We nonetheless store the variable anyhow, to make it easier to loosen that requirement in the
future. We can do that straightforwardly by adding a hashmap that maps each variable to the
corresponding index.
-/

inductive PogElt where
  | var  : Var → PogElt
  | disj : Var → ILit → ILit → PogElt
  | conj : Var → Array ILit → PogElt
deriving Repr, DecidableEq, Inhabited

namespace PogElt

inductive PogEqCases (pogElt : PogElt): Prop where
  | eq_var  (x : Var)                     : pogElt = var n → PogEqCases pogElt
  | eq_disj (x : Var) (left right : ILit) : pogElt = disj n left right → PogEqCases pogElt
  | eq_conj (x : Var) (args : Array ILit) : pogElt = conj n args → PogEqCases pogElt

open PogEqCases in
theorem toEqCases (pogElt : PogElt) : PogEqCases pogElt := by
  cases pogElt
  . case var n => exact eq_var n rfl
  . case disj n left right => exact eq_disj n left right rfl
  . case conj n args => exact eq_conj n args rfl

def varNum : PogElt → Var
  | var x      => x
  | disj x _ _ => x
  | conj x _   => x

-- If we generalize to let variables come in any order, we need only change this to add the indexing
-- function and require `index left.var < index n`, etc.

def args_decreasing : PogElt → Prop
  | var _             => true
  | disj n left right => left.var < n ∧ right.var < n
  | conj n args       =>  ∀ i : Fin args.size, args[i].var < n

end PogElt

-- To generalize this, add a hashmap for the indexing function.

structure Pog :=
  (elts : Array PogElt)
  (wf : ∀ i : Fin elts.size, elts[i].args_decreasing)
  (inv : ∀ i : Fin elts.size, elts[i].varNum = succPNat i)

def PogError := String

namespace Pog
open PogElt

def empty : Pog where
  elts := #[]
  wf := fun i => i.elim0
  inv := fun i => i.elim0

def push (pog : Pog) (pogElt : PogElt)
    (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size) : Pog where
  elts := pog.elts.push pogElt
  wf := by
    intro ⟨i, h'⟩
    rw [Array.size_push] at h'
    cases (lt_or_eq_of_le (le_of_lt_succ h'))
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
      cases (lt_or_eq_of_le (le_of_lt_succ h'))
      . case inl h' =>
        dsimp
        rw [Array.get_push_lt _ _ _ h']
        apply pog.inv ⟨i, h'⟩
      . case inr h' =>
        cases h'
        dsimp
        rw [Array.get_push_eq, hinv]

theorem get_push_elts_lt (pog : Pog) (pogElt : PogElt)
      (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size)
      (i : Nat) (h : i < pog.elts.size) (h' : i < (pog.push pogElt hwf hinv).elts.size) :
    (pog.push pogElt hwf hinv).elts[i] = pog.elts[i] :=
  Array.get_push_lt _ _ _ h

def addVar (pog : Pog) (x : Var) : Except PogError Pog :=
  if h : x = succPNat pog.elts.size then
    .ok <| pog.push (var x) (by trivial) h
  else
    .error s!"Pog variable {x} added, {pog.elts.size + 1} expected"

def addDisj (pog : Pog) (x : Var) (left right : ILit) : Except PogError Pog :=
  if h : x = succPNat pog.elts.size then
    if hleft : left.var < x then
      if hright : right.var < x then
        .ok <| pog.push (disj x left right) ⟨hleft, hright⟩ h
      else
        .error "Pog disjunction {n} added, right argument {right} missing"
    else
      .error <| "Pog disjunction {n} added, left argument {left} missing"
  else
    .error "Pog disjunction {n} added, {pog.elts.size + 1} expected"

def addConj (pog : Pog)(x : Var) (args : Array ILit)  : Except PogError Pog :=
  if h : x = succPNat pog.elts.size then
    if hargs : ∀ i : Fin args.size, args[i].var < x then
      .ok <| pog.push (conj x args) hargs h
    else
      .error "Pog conjunction {n} added, argument missing"
  else
    .error "Pog conjunction {n} added, {pog.elts.size + 1} expected"

def toPropForm (pog : Pog) (l : ILit) : PropForm Var :=
  let i := l.var.natPred
  if h : i < pog.elts.size then
    let propForm := aux pog i h
    cond l.polarity propForm propForm.neg
  else
    cond l.polarity (PropForm.var l.var) (PropForm.var l.var).neg
where
  aux (pog : Pog) : (i : Nat) → i < pog.elts.size → PropForm Var
  | i, h =>
    match pog.elts[i], pog.wf ⟨i, h⟩, pog.inv ⟨i, h⟩ with
    | var x, _, _ => PropForm.var x
    | disj x left right, ⟨hleft, hright⟩, hinv =>
      have h_left_lt : left.var.natPred < i := by
        rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv]
      have h_right_lt : right.var.natPred < i := by
        rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv]
      let newLeft := cond left.polarity (aux pog _ (h_left_lt.trans h))
        (aux pog _ (h_left_lt.trans h)).neg
      let newRight := cond right.polarity (aux pog _ (h_right_lt.trans h))
        (aux pog _ (h_right_lt.trans h)).neg
      newLeft.disj newRight
    | conj n args, _, _ => sorry

theorem toPropFormAux_push_of_lt (pog : Pog) (pogElt : PogElt)
      (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size) :
    (i : Nat) → (h : i < pog.elts.size) → (h' : i < (pog.push pogElt hwf hinv).elts.size) →
     toPropForm.aux (pog.push pogElt hwf hinv) i h' = toPropForm.aux pog i h
  | i, h, h' => by
    rw [toPropForm.aux]
    split
    . next x hxeq hh f g =>
      rw [pog.get_push_elts_lt pogElt hwf hinv i h h'] at hh
      conv => rhs; rw [toPropForm.aux]
      split <;> simp [*] at *
      rw [hh]
    . next x left right hleft hright hxeq hh f g =>
      rw [pog.get_push_elts_lt pogElt hwf hinv i h h'] at hh
      dsimp [varNum] at hxeq
      conv => rhs; rw [toPropForm.aux]
      split
      . simp [hh] at *
      . next x' left' right' hleft' hright' hxeq' hh' f' g' =>
        rw [hh] at hh'
        injection hh'
        next heq1 heq2 heq3 =>
        cases heq1
        cases heq2
        cases heq3
        dsimp
        have : PNat.natPred (ILit.var left) < i := by
          rwa [←succPNat_lt_succPNat, ←hxeq, PNat.succPNat_natPred]
        have : PNat.natPred (ILit.var right) < i := by
          rwa [←succPNat_lt_succPNat, ←hxeq, PNat.succPNat_natPred]
        rw [toPropFormAux_push_of_lt pog pogElt hwf hinv (PNat.natPred (ILit.var left)),
            toPropFormAux_push_of_lt pog pogElt hwf hinv (PNat.natPred (ILit.var right))]
      . simp [hh] at *
    . sorry

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

/-
def toPropFormArray (pog : Pog) : { A : Array (PropForm Var) // A.size = pog.elts.size } :=
  toPropFormArrayAux pog pog.elts.size #[] (by rw [add_comm]; rfl)
where
  toPropFormArrayAux (pog : Pog) :
      (n : Nat) → (A : Array (PropForm Var)) → (pog.elts.size = A.size + n) →
        { A : Array (PropForm Var) // A.size = pog.elts.size }
  | 0, A, h => by
    use A
    exact h.symm
  | n + 1, A, h =>
    have ASizeLt : A.size < pog.elts.size := by
      rw [h, ←add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    let nextElt : PropForm Var :=
      match pog.elts[A.size]'ASizeLt, pog.wf ⟨A.size, ASizeLt⟩, pog.inv ⟨A.size, ASizeLt⟩ with
        | var x, _, _ => PropForm.var x
        | disj x left right, ⟨hleft, hright⟩, hinv =>
          have h_left_lt : left.var.natPred < A.size := by
            rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv]
          have h_right_lt : right.var.natPred < A.size := by
            rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv]
          let newLeft := cond left.polarity A[left.var.natPred] A[left.var.natPred].neg
          let newRight := cond right.polarity A[right.var.natPred] A[right.var.natPred].neg
          newLeft.disj newRight
        | conj n args, hwf, hinv => sorry
    toPropFormArrayAux pog n (A.push nextElt) (by rw [Array.size_push, h, add_assoc, add_comm 1])

def toPropForm (pog : Pog) (l : ILit) : PropForm Var :=
  let i := l.var.natPred
  if h : i < pog.elts.size then
    let A := pog.toPropFormArray
    have : i < A.val.size := by rwa [A.property]
    cond l.polarity A.val[i] A.val[i].neg
  else
    cond l.polarity (PropForm.var l.var) (PropForm.var l.var).neg

theorem toPropFormArrayAux_correct (pog : Pog) :
    (n : Nat) → (A : Array Nat) → (h : pog.elts.size = A.size + n) :
  ∀ i : Fin (pog.toPropFormArrayAux).val.size

--theorem toPropFormArray_correct (pog : Pog) : ∀ i : Fin { A : Array (PropForm Var) // A.size = pog.elts.size } := sorry
-/


/-
Even though we are not using this now, a Pog can keep track of its variables, and if the client
can ensure that conjunctions and disjunctions refer to previous variables, we can eliminate the
checks in `addDisj` and `addConj`.
-/

def vars (pog : Pog) : Finset Var := Finset.range pog.elts.size |>.image succPNat

theorem mem_vars_aux {pog : Pog} {n : Var} : n ∈ pog.vars ↔ n ≤ pog.elts.size := by
  simp only [Pog.vars, Finset.mem_image, Finset.mem_range]
  constructor
  . rintro ⟨m, hm, rfl⟩
    exact hm
  . rintro hle
    use n.natPred
    rw [lt_iff_add_one_le, ←succ_eq_add_one, ←succPNat_coe, PNat.succPNat_natPred]
    exact ⟨hle, rfl⟩

theorem mem_vars {pog : Pog} {n : Var} :
    n ∈ pog.vars ↔ ∃ i : Fin pog.elts.size, pog.elts[i].varNum = n := by
  rw [mem_vars_aux]
  constructor
  . intro hle
    have : n.natPred < pog.elts.size := by
      apply lt_of_succ_le
      rw [←succPNat_coe, PNat.succPNat_natPred]
      exact hle
    use ⟨n.natPred, this⟩
    rw [pog.inv, PNat.succPNat_natPred]
  . rintro ⟨i, rfl⟩
    rw [pog.inv, succPNat_coe]
    exact i.isLt

theorem vars_push (pog : Pog) (pogElt : PogElt)
      (hwf : args_decreasing pogElt) (hinv : pogElt.varNum = succPNat pog.elts.size) :
    vars (pog.push pogElt hwf hinv) = insert (succPNat pog.elts.size) pog.vars := by
  ext i
  rw [mem_vars_aux, Pog.push, Array.size_push, Finset.mem_insert, mem_vars_aux,
          le_iff_eq_or_lt, ←Nat.lt_succ, ←succ_eq_add_one, ←succPNat_coe, PNat.coe_inj]

theorem vars_addVar {pog newPog : Pog} {n : Var} (h : (pog.addVar n) = .ok newPog) :
    newPog.vars = insert n pog.vars := by
  rw [addVar] at h
  split at h
  case inr h' =>
    contradiction
  case inl h' =>
    ext i
    injection h with h
    rw [←h, vars_push, h']

theorem vars_addDisj {pog newPog : Pog} {n : Var} (left right : ILit)
      (h : (pog.addDisj n left right) = .ok newPog) :
    newPog.vars = insert n pog.vars := by
  rw [addDisj] at h
  split at h <;> try { contradiction }
  split at h <;> try { contradiction }
  split at h <;> try { contradiction }
  next h' _ _ =>
    ext i
    injection h with h
    rw [←h, vars_push, h']

theorem vars_addConj {pog newPog : Pog} {n : Var} (args : Array ILit)
      (h : (pog.addConj n args) = .ok newPog) :
    newPog.vars = insert n pog.vars := by
  rw [addConj] at h
  split at h <;> try { contradiction }
  split at h <;> try { contradiction }
  next h' _ =>
    ext i
    injection h with h
    rw [←h, vars_push, h']

end Pog