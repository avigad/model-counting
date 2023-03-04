import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.PNat.Basic
import ProofChecker.Data.ICnf
import ProofChecker.CountModels

open Nat
abbrev Cube := Array ILit

namespace PropForm

def bigConj (as : Array (PropForm Var)) : PropForm Var :=
  match h: as.size with
    | 0 => tr
    | n+1 =>
      have : as.size - 1 < as.size := by rw [h]; exact lt_succ_self _
      as.foldr (f := PropForm.conj) (init := as[as.size - 1]) (start:= as.size - 1)

def withPolarity (p : PropForm Var) (l : ILit) := cond (l.polarity) p p.neg

@[simp] theorem withPolarity_mkPos (p : PropForm Var) (x : Var) :
  withPolarity p (.mkPos x) = p := by simp [withPolarity]

@[simp] theorem withPolarity_mkNeg (p : PropForm Var) (x : Var) :
  withPolarity p (.mkNeg x) = p.neg := by simp [withPolarity]

end PropForm

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
  | conj : Var → Cube → PogElt
deriving Repr, DecidableEq, Inhabited

namespace PogElt

/-
-- Not sure if these are needed.
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
-/

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

lemma get_push_elts_nat_Pred_varNum (pog : Pog) (pogElt : PogElt)
      (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size)
      (h' : PNat.natPred (varNum pogElt) < Array.size (push pog pogElt hwf hinv).elts) :
    (pog.push pogElt hwf hinv).elts[PNat.natPred pogElt.varNum] = pogElt := by
  simp only [hinv, natPred_succPNat]
  apply Array.get_push_eq

def size_push_elts (pog : Pog) (pogElt : PogElt)
      (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size) :
    (pog.push pogElt hwf hinv).elts.size = pog.elts.size + 1 :=
  Array.size_push _ _

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

def addConj (pog : Pog)(x : Var) (args : Cube)  : Except PogError Pog :=
  if h : x = succPNat pog.elts.size then
    if hargs : ∀ i : Fin args.size, args[i].var < x then
      .ok <| pog.push (conj x args) hargs h
    else
      .error "Pog conjunction {n} added, argument missing"
  else
    .error "Pog conjunction {n} added, {pog.elts.size + 1} expected"

def toPropForm (pog : Pog) (l : ILit) : PropForm Var :=
  if h : l.var.natPred < pog.elts.size then
    aux pog l.var.natPred h |>.withPolarity l
  else
    l.toPropForm
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
      let newLeft := aux pog _ (h_left_lt.trans h) |>.withPolarity left
      let newRight := aux pog _ (h_right_lt.trans h) |>.withPolarity right
      PropForm.disj newLeft newRight
    | conj x args, hwf, hinv => by
      let newArgs : Array (PropForm Var) :=
        Array.ofFn fun (j : Fin args.size) =>
          have h_lt : args[j].var.natPred < i := by
            rw [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv]
            exact hwf j
          aux pog args[j].var.natPred (h_lt.trans h) |>.withPolarity args[j]
      exact PropForm.bigConj newArgs

theorem toPropForm_push_of_lt (pog : Pog) (pogElt : PogElt)
      (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size)
      (l : ILit) (hl : PNat.natPred l.var < pog.elts.size) :
    (pog.push pogElt hwf hinv).toPropForm l = pog.toPropForm l := by
  have hl' : PNat.natPred l.var < (pog.push pogElt hwf hinv).elts.size := by
    dsimp [Pog.push]; rw [Array.size_push]; exact hl.trans (lt_succ_self _)
  rw [toPropForm, toPropForm, dif_pos hl, dif_pos hl', aux]
where
  aux :
    (i : Nat) → (h : i < pog.elts.size) → (h' : i < (pog.push pogElt hwf hinv).elts.size) →
     toPropForm.aux (pog.push pogElt hwf hinv) i h' = toPropForm.aux pog i h
  | i, h, h' => by
    rw [toPropForm.aux]; conv => rhs; rw [toPropForm.aux]
    have heq := pog.get_push_elts_lt pogElt hwf hinv i h h'
    split <;> split <;> simp [*] at heq <;> try { injection heq } <;> try { simp only [heq] }
    . next x left right hleft hright hinv' _ _ _ =>
      simp only [heq]
      have _ : left.var.natPred < i := by
        rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv']
      have _ : right.var.natPred < i := by
        rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv']
      rw [aux (PNat.natPred (ILit.var left)), aux (PNat.natPred (ILit.var right))]
    . next x args hargs hinv _ _ _ _ _ _ x' args' _ _ _ _ _ =>
      cases heq.2
      cases heq.1
      apply congr_arg PropForm.bigConj
      apply congr_arg Array.ofFn
      ext j; dsimp
      have _ : args[j].var.natPred < i := by
        rw [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←hinv]
        exact hargs j
      rw [aux (PNat.natPred (ILit.var _))]

theorem toPropForm_push_of_ne (y : Var) (pog : Pog) (pogElt : PogElt)
      (hwf : pogElt.args_decreasing) (hinv : pogElt.varNum = succPNat pog.elts.size)
      (hne : pogElt.varNum ≠ y) :
    (pog.push pogElt hwf hinv).toPropForm (.mkPos y) = pog.toPropForm (.mkPos y) := by
  rw [toPropForm, toPropForm]
  simp only [ILit.var_mkPos, PropForm.withPolarity_mkPos]
  cases le_or_gt pogElt.varNum y
  case inl hle =>
    have : Array.size pog.elts ≤ PNat.natPred y :=
      by rwa [←succPNat_le_succPNat, ←hinv, PNat.succPNat_natPred]
    rw [dif_neg (not_lt_of_le this), dif_neg]
    rw [not_lt, size_push_elts, succ_le_iff]
    apply (lt_of_le_of_ne this)
    contrapose! hne
    rw [hinv, hne, PNat.succPNat_natPred]
  case inr hle =>
    have : PNat.natPred y < Array.size pog.elts :=
      by rwa [←succPNat_lt_succPNat, ←hinv, PNat.succPNat_natPred]
    rw [dif_pos this, dif_pos, toPropForm_push_of_lt.aux]
    rw [size_push_elts]
    apply lt_succ_of_lt this

theorem toPropForm_neg (p : Pog) (x : Var) :
    p.toPropForm (.mkNeg x) = .neg (p.toPropForm (.mkPos x)) := by
  rw [toPropForm, toPropForm]; simp; split <;> simp [ILit.toPropForm]

theorem toPropForm_addVar (p p' : Pog) (x : Var) :
    p.addVar x = .ok p' →
    p'.toPropForm (.mkPos x) = .var x := by
  rw [addVar]
  split
  . next h =>
    intro h'
    injection h' with h'
    rw [←h', toPropForm]
    split
    . next h'' =>
      rw [toPropForm.aux]
      have heq : ∀ h1 h2,
          (push p (var x) h1 h2).elts[PNat.natPred (ILit.var (ILit.mkPos x))] = var x :=
        fun h1 h2 => get_push_elts_nat_Pred_varNum _ _ _ _ _
      split <;> simp only [heq] at *
      next x' _ _ _ _ heq' =>
        injection heq' with heq'
        simp [heq']
    . simp [ILit.toPropForm]
  . intro; contradiction

theorem toPropForm_addVar_of_ne (x y : Var) (p p' : Pog) :
    p.addVar x = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y) := by
  rw [addVar]
  split
  . next h =>
    intro h'
    injection h' with h'
    intro hne
    rw [←h']
    apply toPropForm_push_of_ne
    exact hne
  . intro; contradiction

theorem toPropForm_addDisj (x : Var) (l₁ l₂ : ILit) (p p' : Pog) :
    p.addDisj x l₁ l₂ = .ok p' →
    p'.toPropForm (.mkPos x) = .disj (p.toPropForm l₁) (p.toPropForm l₂) := by
  rw [addDisj]
  split
  . next h =>
    split
    . next hleft =>
      split
      . next hright =>
          intro h'
          injection h' with h'
          rw [←h', toPropForm]
          split
          . next h'' =>
            rw [toPropForm.aux]
            have heq : ∀ h1 h2,
                (push p (disj x l₁ l₂) h1 h2).elts[PNat.natPred (ILit.var (ILit.mkPos x))] =
                  disj x l₁ l₂ :=
              fun h1 h2 => get_push_elts_nat_Pred_varNum _ _ _ _ _
            split <;> simp only [heq] at *
            next x' left' right' _ _ _ _ _ heq' =>
              injection heq' with heq₁ heq₂ heq₃
              cases heq₁
              cases heq₂
              cases heq₃
              simp only [PropForm.withPolarity_mkPos, PropForm.disj.injEq]
              constructor
              . rw [toPropForm, dif_pos, toPropForm_push_of_lt.aux]
                rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←h]
              . rw [toPropForm, dif_pos, toPropForm_push_of_lt.aux]
                rwa [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←h]
          . next h'' =>
            exfalso
            apply h''
            rw [size_push_elts, h, ILit.var_mkPos, natPred_succPNat]
            exact lt_succ_self _
      . intro; contradiction
    . intro; contradiction
  . intro; contradiction

theorem toPropForm_addDisj_of_ne (x y : Var) (l₁ l₂ : ILit) (p p' : Pog) :
    p.addDisj x l₁ l₂ = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y) := by
  rw [addDisj]
  split
  . next h =>
    split
    . next hleft =>
      split
      . next hright =>
          intro h'
          injection h' with h'
          intro hne
          rw [←h']
          apply toPropForm_push_of_ne
          exact hne
      . intro; contradiction
    . intro; contradiction
  . intro; contradiction

theorem toPropForm_addConj (x : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' →
    p'.toPropForm (.mkPos x) =
      -- NOTE: This could change, and the `.tr` part is awkward. Should we have one canonical way
      -- to structurally turn a cube into a PropForm?
      ls.foldl (init := .tr) (fun acc l => acc.conj (p.toPropForm l)) := sorry

/-
Need this form...
theorem toPropForm_addConj (x : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' →
    p'.toPropForm (.mkPos x) =
      -- NOTE: This could change, and the `.tr` part is awkward. Should we have one canonical way
      -- to structurally turn a cube into a PropForm?
      ls.foldl (init := .tr) (fun acc l => acc.conj (p.toPropForm l)) := sorry
-/

theorem toPropForm_addConj_of_ne (x y : Var) (ls : Array ILit) (p p' : Pog) :
    p.addConj x ls = .ok p' → x ≠ y →
    p'.toPropForm (.mkPos y) = p.toPropForm (.mkPos y) := by
  rw [addConj]
  split
  . next h =>
    split
    . next args =>
        intro h'
        injection h' with h'
        intro hne
        rw [←h']
        apply toPropForm_push_of_ne
        exact hne
    . intro; contradiction
  . intro; contradiction

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