import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Basic
import ProofChecker.Data.ICnf
import ProofChecker.CountModels

open Nat
abbrev Cube := Array ILit

namespace ILit

theorem mkPos_var_true (l : ILit) (h : l.polarity = true) :
    mkPos (var l) = l := by
  conv => rhs; rw [←eta l]; simp [h, mk]

theorem mkPos_var_false (l : ILit) (h : l.polarity = false) :
    mkPos (var l) = -l := by
  conv => rhs; rw [←eta_neg l]; simp [h, mk]

end ILit

namespace PropForm

def listConj (φs : List (PropForm Var)) : PropForm Var :=
  φs.foldr (init := .tr) (f := .conj)

lemma mem_vars_foldr_conj (φs : List (PropForm Var)) (x : Var) :
    x ∈ (φs.foldr (init := PropForm.tr) (f := .conj)).vars ↔
      ∃ i : Fin (φs.length), x ∈ (φs.get i).vars := by
  induction φs
  . simp [PropForm.vars]
  . next φ φs ih =>
    simp [PropForm.vars, ih, Fin.exists_fin_succ]

theorem decomposable_listConj (φs : List (PropForm Var)) :
    (listConj φs).decomposable ↔
      ∀ i : Fin φs.length, (φs.get i).decomposable ∧
      ∀ j : Fin φs.length, i ≠ j → (φs.get i).vars ∩ (φs.get j).vars = ∅ := by
  induction φs
  . dsimp [listConj, decomposable]; simp
  . next φ φs ih =>
    dsimp [listConj, decomposable] at *
    simp only [ih, Finset.inter_self, List.get, not_true, IsEmpty.forall_iff, true_and,
      add_eq, add_zero, Fin.eta, mem_vars_foldr_conj, Fin.forall_fin_succ]
    have aux : vars φ ∩ vars (List.foldr conj tr φs) = ∅ ↔
        ∀ i : Fin (List.length φs), vars φ ∩ vars (List.get φs i) = ∅ := by
      simp only [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter, not_and, mem_vars_foldr_conj,
        not_exists]
      aesop
    have aux2 : ∀ i : Fin (List.length φs),
        vars (List.get φs i) ∩ vars φ = vars φ ∩ vars (List.get φs i) := by
      intro i; rw [Finset.inter_comm]
    have aux3 : ∀ i : Fin (List.length φs), ¬ 0 = Fin.succ i := by
      intro i; apply Ne.symm; apply Fin.succ_ne_zero
    aesop

def arrayConj (φs : Array (PropForm Var)) : PropForm Var := listConj φs.data

theorem decomposable_arrayConj (φs : Array (PropForm Var)) :
    (arrayConj φs).decomposable ↔
      ∀ i : Fin φs.size, (φs[i]).decomposable ∧
      ∀ j : Fin φs.size, i ≠ j → (φs[i]).vars ∩ (φs[j]).vars = ∅ := by
  dsimp [arrayConj]; rw [decomposable_listConj]; rfl

def arrayConjTerm (φs : Array (PropForm Var)) : PropTerm Var :=
  φs.data.foldr (init := ⊤) (f := fun φ acc => ⟦φ⟧ ⊓ acc)

@[simp]
theorem mk_arrayConj (φs : Array (PropForm Var)) : ⟦arrayConj φs⟧ = arrayConjTerm φs := by
  dsimp [arrayConj, listConj, arrayConjTerm]
  induction φs.data <;> simp_all

open PropTerm in
theorem satisfies_arrayConjTerm (φs : Array (PropForm Var)) (τ : PropAssignment Var) :
    τ ⊨ arrayConjTerm φs ↔ ∀ φ ∈ φs.data, τ ⊨ ⟦φ⟧ := by
  dsimp [arrayConjTerm]
  induction φs.data <;> aesop

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
  (inv : ∀ i : Fin elts.size, i = elts[i].varNum.natPred)

def PogError := String

instance : ToString PogError where
  toString := id

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
      dsimp; rw [Array.get_push_lt _ _ _ h']
      apply pog.wf ⟨i, h'⟩
    . case inr h' =>
      dsimp; cases h'; rw [Array.get_push_eq]
      exact hwf
  inv := by
      intro ⟨i, h'⟩
      rw [Array.size_push] at h'
      cases (lt_or_eq_of_le (le_of_lt_succ h'))
      . case inl h' =>
        dsimp; rw [Array.get_push_lt _ _ _ h']
        apply pog.inv ⟨i, h'⟩
      . case inr h' =>
        cases h'; dsimp
        rw [Array.get_push_eq, hinv, natPred_succPNat]

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
        .error s!"Pog disjunction {x} added, right argument {right} missing"
    else
      .error s!"Pog disjunction {x} added, left argument {left} missing"
  else
    .error s!"Pog disjunction {x} added, {pog.elts.size + 1} expected"

def addConj (pog : Pog)(x : Var) (args : Cube)  : Except PogError Pog :=
  if h : x = succPNat pog.elts.size then
    if hargs : ∀ i : Fin args.size, args[i].var < x then
      .ok <| pog.push (conj x args) hargs h
    else
      .error s!"Pog conjunction {x} added, argument missing"
  else
    .error s!"Pog conjunction {x} added, {pog.elts.size + 1} expected"

/-- This avoids having to repeat a calculation. -/
lemma lt_aux {n : Nat} {y : Var} (hlt: y < x) (hinv: n = x.natPred) :
  y.natPred < n := by rwa [hinv, PNat.natPred_lt_natPred]

def toPropForm (pog : Pog) (l : ILit) : PropForm Var :=
  if h : l.var.natPred < pog.elts.size then
    aux l.var.natPred h |>.withPolarity l
  else
    l.toPropForm
where
  aux : (i : Nat) → i < pog.elts.size → PropForm Var
  | i, h =>
    match pog.elts[i], pog.wf ⟨i, h⟩, pog.inv ⟨i, h⟩ with
    | var x, _, _ => PropForm.var x
    | disj x left right, ⟨hleft, hright⟩, hinv =>
        have h_left_lt : left.var.natPred < i := lt_aux hleft hinv
        have h_right_lt : right.var.natPred < i := lt_aux hright hinv
        .disj (aux _ (h_left_lt.trans h) |>.withPolarity left)
              (aux _ (h_right_lt.trans h) |>.withPolarity right)
    | conj x args, hwf, hinv =>
        .arrayConj <| Array.ofFn fun (j : Fin args.size) =>
          have h_lt : args[j].var.natPred < i := lt_aux (hwf j) hinv
          aux args[j].var.natPred (h_lt.trans h) |>.withPolarity args[j]

theorem toPropForm_of_polarity_eq_false (pog : Pog) (l : ILit) (hl : l.polarity = false) :
    pog.toPropForm l = .neg (pog.toPropForm (-l)) := by
  rw [toPropForm]
  split
  . next h =>
    rw [toPropForm, ILit.var_negate, dif_pos h, PropForm.withPolarity, hl, cond_false,
      PropForm.withPolarity, ILit.polarity_negate, hl, Bool.not_false, cond_true]
  . next h =>
    rw [toPropForm, ILit.var_negate, dif_neg h]
    rw [ILit.toPropForm, hl]; simp only [ite_false, PropForm.neg.injEq]
    rw [ILit.toPropForm, ILit.polarity_negate, hl]; simp only [ILit.var_negate, ite_true]

theorem toPropForm_aux_eq (pog : Pog) (i : Nat) (h : i < pog.elts.size) :
  toPropForm.aux pog i h =
    match pog.elts[i] with
      | var x => PropForm.var x
      | disj _ left right => .disj (pog.toPropForm left) (pog.toPropForm right)
      | conj _ args =>
          .arrayConj <| Array.ofFn fun (j : Fin args.size) => pog.toPropForm args[j] := by
  rw [toPropForm.aux]
  split
  . simp [*]
  . next x left right hleft hright hinv heq _ _ =>
    simp only [heq]
    have h_left_lt : left.var.natPred < i := lt_aux hleft hinv
    have h_right_lt : right.var.natPred < i := lt_aux hright hinv
    rw [toPropForm, dif_pos (h_left_lt.trans h), toPropForm, dif_pos (h_right_lt.trans h)]
  . next x args hwf hinv heq _ _ =>
    simp only [heq]
    congr; ext j
    have h_lt : args[j].var.natPred < i := lt_aux (hwf j) hinv
    rw [toPropForm, dif_pos (h_lt.trans h)]

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
        dsimp at hinv'; rwa [hinv', PNat.natPred_lt_natPred]
      have _ : right.var.natPred < i := by
        dsimp at hinv'; rwa [hinv', PNat.natPred_lt_natPred]
      rw [aux (PNat.natPred (ILit.var left)), aux (PNat.natPred (ILit.var right))]
    . next x args hargs hinv' _ _ _ _ _ _ x' args' _ _ _ _ _ =>
      cases heq.2
      cases heq.1
      apply congr_arg PropForm.arrayConj
      apply congr_arg Array.ofFn
      ext j; dsimp
      have _ : args[j].var.natPred < i := by
        dsimp at hinv'; rw [hinv', PNat.natPred_lt_natPred]
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
    
theorem toPropForm_empty (l : ILit) : empty.toPropForm l = l.toPropForm := by
  dsimp [toPropForm]
  split
  next h =>
    simp [empty] at h
  next =>
    rfl

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
  
theorem toPropForm_addVar_lit (p p' : Pog) (l : ILit) :
    p.addVar l.var = .ok p' →
    p'.toPropForm l = l.toPropForm := by
  cases l.mkPos_or_mkNeg <;>
    next hMk =>
      intro h
      rw [hMk]
      have := toPropForm_addVar _ _ _ h
      simp [toPropForm_neg, this]

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
  
theorem toPropForm_addVar_lit_of_ne (x : Var) (l : ILit) (p p' : Pog) :
    p.addVar x = .ok p' → x ≠ l.var →
    p'.toPropForm l = p.toPropForm l := by
  cases l.mkPos_or_mkNeg <;>
    next hMk =>
      intro h hNe
      rw [hMk]
      have := toPropForm_addVar_of_ne _ _ _ _ h hNe
      simp [toPropForm_neg, this]

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
    p'.toPropForm (.mkPos x) = .arrayConj (ls.map p.toPropForm) := by
  rw [addConj]
  split
  . next h =>
    split
    . next hargs =>
        intro h'
        injection h' with h'
        rw [←h', toPropForm]
        split
        . next h'' =>
          rw [toPropForm.aux]
          have heq : ∀ h1 h2,
              (push p (conj x ls) h1 h2).elts[PNat.natPred (ILit.var (ILit.mkPos x))] =
                conj x ls :=
            fun h1 h2 => get_push_elts_nat_Pred_varNum _ _ _ _ _
          split <;> simp only [heq] at *
          next x' ls' _ _ _ _ _ heq' =>
            injection heq' with heq₁ heq₂
            cases heq₁
            cases heq₂
            simp only [PropForm.withPolarity_mkPos, PropForm.conj.injEq]
            congr
            apply Array.ext
            . rw [Array.size_map, Array.size_ofFn]
            . intro j hj₁ hj₂
              simp only [getElem_fin, Array.getElem_ofFn, Array.getElem_map]
              rw [toPropForm, dif_pos, toPropForm_push_of_lt.aux]
              rw [←succPNat_lt_succPNat, PNat.succPNat_natPred, ←h]
              rw [Array.size_ofFn] at hj₁
              apply hargs ⟨j, hj₁⟩
        . next h'' =>
          exfalso
          apply h''
          rw [size_push_elts, h, ILit.var_mkPos, natPred_succPNat]
          exact lt_succ_self _
    . intro; contradiction
  . intro; contradiction

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

-- This can be optimized to eliminate the first multiplication / division.
-- We can also avoid creating the array and compute the result with a loop.
def conjProd (nVars : Nat) {n : Nat} (g : Fin n → Nat) : Nat :=
  (Array.ofFn g).foldr (init := 2^nVars) (f := fun a b => a * b / 2^nVars)

-- This shouldn't be used for computation, but we have more theorems about lists.
def conjProd' (nVars : Nat) {n : Nat} (g : Fin n → Nat) : Nat :=
  (List.ofFn g).foldr (init := 2^nVars) (f := fun a b => a * b / 2^nVars)

theorem conjProd_eq_conjProd' : conjProd = conjProd' := by
  ext nVars n f
  rw [conjProd, conjProd', Array.foldr_eq_foldr_data, List.ofFn, Array.toList_eq]

def toCountArray (pog : Pog) (nVars : Nat) :
    { A : Array Nat // A.size = pog.elts.size } :=
  aux pog.elts.size #[] (by rw [add_comm]; rfl)
where
  aux : (n : Nat) → (A : Array Nat) → (pog.elts.size = A.size + n) →
        { A : Array Nat // A.size = pog.elts.size }
  | 0, A, h => ⟨A, h.symm⟩
  | n + 1, A, h =>
    have ASizeLt : A.size < pog.elts.size := by
      rw [h, ←add_assoc]; exact lt_succ_of_le (le_add_right _ _)
    let nextElt : Nat :=
      match pog.elts[A.size]'ASizeLt, pog.wf ⟨A.size, ASizeLt⟩, pog.inv ⟨A.size, ASizeLt⟩ with
        | var x, _, _ => 2^(nVars - 1)
        | disj x left right, ⟨hleft, hright⟩, hinv =>
          have := lt_aux hleft hinv
          have := lt_aux hright hinv
          let lmodels :=
            if left.polarity then A[left.var.natPred] else 2^nVars - A[left.var.natPred]
          let rmodels :=
            if right.polarity then A[right.var.natPred] else 2^nVars - A[right.var.natPred]
          lmodels + rmodels
        | conj n args, hwf, hinv =>
          conjProd nVars fun (j : Fin args.size) =>
              have := lt_aux (hwf j) hinv
              if args[j].polarity then A[args[j].var.natPred] else 2^nVars - A[args[j].var.natPred]
    aux n (A.push nextElt) (by rw [Array.size_push, h, add_assoc, add_comm 1])

def count (pog : Pog) (nVars : Nat) (x : Var) : Nat :=
  if h : x.natPred < pog.elts.size then
    have : x.natPred < (pog.toCountArray nVars).1.size := by
      rwa [(pog.toCountArray nVars).2]
    (pog.toCountArray nVars).1[x.natPred]
  else
    PropForm.countModels nVars (ILit.mkPos x).toPropForm

theorem countModels_foldr_conj (nVars : Nat) (φs : List (PropForm Var)) :
   PropForm.countModels nVars (List.foldr PropForm.conj PropForm.tr φs) =
      List.foldr (fun a b => a * b / 2 ^ nVars) (2 ^ nVars)
        (φs.map (PropForm.countModels nVars)) := by
  induction φs
  . simp [PropForm.countModels]
  . next φ φs ih =>
    rw [List.foldr_cons, PropForm.countModels, ih, List.map, List.foldr]

theorem toCountArray_spec (pog : Pog) (nVars : Nat) :
  ∀ i : Fin (pog.toCountArray nVars).1.size,
      (pog.toCountArray nVars).1[i] =
        PropForm.countModels nVars (pog.toPropForm (.mkPos (succPNat i))) := by
  apply aux
  rintro ⟨i, h⟩; contradiction
where
  aux : (n : Nat) → (A : Array Nat) → (h : pog.elts.size = A.size + n) →
          (h' : (∀ i : Fin A.size, A[i] =
            PropForm.countModels nVars (pog.toPropForm (.mkPos (succPNat i))))) →
    ∀ i : Fin (toCountArray.aux pog nVars n A h).1.size,
      (toCountArray.aux pog nVars n A h).1[i] =
        PropForm.countModels nVars (pog.toPropForm (.mkPos (succPNat i)))
  | 0,     _, _, h' => h'
  | n + 1, A, h, h' => by
    have ASizeLt : A.size < pog.elts.size := by
      rw [h, ←add_assoc]; exact lt_succ_of_le (le_add_right _ _)
    apply aux n; dsimp
    intro ⟨i, i_lt⟩
    rw [Array.size_push] at i_lt
    cases lt_or_eq_of_le (le_of_lt_succ i_lt)
    next ilt =>
      rw [Array.get_push_lt _ _ i ilt]
      exact h' ⟨i, ilt⟩
    next ieq =>
      simp only [ieq, Array.get_push_eq]
      split
      . next x _ hinv heq _ _ =>
        rw [toPropForm]
        simp only [ILit.var_mkPos, natPred_succPNat, PropForm.withPolarity_mkPos, dif_pos ASizeLt]
        rw [toPropForm_aux_eq, heq, PropForm.countModels]
      . next x left right hleft hright hinv heq _ _ =>
        rw [toPropForm]
        simp only [ILit.var_mkPos, natPred_succPNat, PropForm.withPolarity_mkPos, dif_pos ASizeLt]
        have hleft : PNat.natPred (ILit.var left) < A.size := by
          dsimp at hinv; rwa [hinv, PNat.natPred_lt_natPred]
        have hright : PNat.natPred (ILit.var right) < A.size := by
          dsimp at hinv; rwa [hinv, PNat.natPred_lt_natPred]
        have hl := h' ⟨_, hleft⟩; dsimp at hl; rw [hl]
        have hr := h' ⟨_, hright⟩; dsimp at hr; rw [hr]
        rw [toPropForm_aux_eq, heq, PropForm.countModels, PNat.succPNat_natPred,
          PNat.succPNat_natPred]
        split
        . next hlp =>
          rw [ILit.mkPos_var_true _ hlp]
          split
          . next hrp =>
            rw [ILit.mkPos_var_true _ hrp]
          . next hrnp =>
            rw [Bool.not_eq_true] at hrnp
            rw [ILit.mkPos_var_false _ hrnp, pog.toPropForm_of_polarity_eq_false _ hrnp,
              PropForm.countModels]
        . next hlnp =>
          rw [Bool.not_eq_true] at hlnp
          rw [ILit.mkPos_var_false _ hlnp, pog.toPropForm_of_polarity_eq_false _ hlnp,
              PropForm.countModels]
          split
          . next hrp =>
            rw [ILit.mkPos_var_true _ hrp]
          . next hrnp =>
            rw [Bool.not_eq_true] at hrnp
            rw [ILit.mkPos_var_false _ hrnp, pog.toPropForm_of_polarity_eq_false _ hrnp,
              PropForm.countModels]
      . next x args hwf hinv heq _ _ =>
        rw [toPropForm]
        simp only [ILit.var_mkPos, natPred_succPNat, PropForm.withPolarity_mkPos, dif_pos ASizeLt]
        rw [toPropForm_aux_eq, heq]; dsimp
        rw [conjProd_eq_conjProd', conjProd', PropForm.arrayConj, PropForm.listConj,
          countModels_foldr_conj]
        apply congr_arg
        rw [←Array.toList_eq, ←List.ofFn, List.map_ofFn]
        apply congr_arg
        ext j
        simp only [Function.comp_apply]
        simp only [ILit.var_mkPos, natPred_succPNat, PropForm.withPolarity_mkPos, dif_pos ASizeLt]
        have harg : PNat.natPred (ILit.var args[j]) < A.size := by
          dsimp at hinv; rw [hinv, PNat.natPred_lt_natPred]
          exact hwf j
        have ha := h' ⟨_, harg⟩; dsimp at ha; rw [ha]
        rw [PNat.succPNat_natPred]
        split
        . next hlp =>
          rw [ILit.mkPos_var_true _ hlp]
        . next hlnp =>
          rw [Bool.not_eq_true] at hlnp
          rw [ILit.mkPos_var_false _ hlnp, pog.toPropForm_of_polarity_eq_false _ hlnp,
              PropForm.countModels]

theorem count_eq_countModels (pog : Pog) (nVars : Nat) (x : Var) :
    pog.count nVars x = (pog.toPropForm (.mkPos x)).countModels nVars := by
  rw [count, toPropForm, ILit.var_mkPos]
  split
  . next h =>
    have h' := h; rw [←(pog.toCountArray nVars).2] at h'
    have := pog.toCountArray_spec nVars ⟨_, h'⟩
    dsimp at this; rw [PNat.succPNat_natPred] at this
    dsimp; rw [this, toPropForm, ILit.var_mkPos, dif_pos h]
  . next h => rfl

theorem count_eq' (pog : Pog) (nVars : Nat) (x : Var) (φ : PropForm Var) :
    pog.toPropForm (.mkPos x) = φ →
    pog.count nVars x = φ.countModels nVars := by intro h; rw [←h, count_eq_countModels]

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
    rw [←PNat.natPred_inj]
    symm; apply pog.inv ⟨n.natPred, this⟩
  . rintro ⟨i, rfl⟩
    have := congr_arg succPNat (pog.inv i)
    rw [PNat.succPNat_natPred] at this
    rw [←this, succPNat_coe]
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