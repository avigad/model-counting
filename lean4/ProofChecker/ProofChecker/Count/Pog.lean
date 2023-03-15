import ProofChecker.Data.Pog
import ProofChecker.Count.PropForm

open Nat
open PogElt

namespace Pog

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
The weighted count function
-/

def conjProdW {n : Nat} (g : Fin n → Rat) : Rat :=
  (Array.ofFn g).foldr (init := 1) (f := fun a b => a * b)

def conjProdW' {n : Nat} (g : Fin n → Rat) : Rat :=
  (List.ofFn g).foldr (init := 1) (f := fun a b => a * b)

theorem conjProdW_eq_conjProdW' : @conjProdW = @conjProdW' := by
  apply funext; intro n
  apply funext; intro g
  rw [conjProdW, conjProdW', Array.foldr_eq_foldr_data, List.ofFn, Array.toList_eq]

def toCountWeightArray (pog : Pog) (weight : Var → Rat) :
    { A : Array Rat // A.size = pog.elts.size } :=
  aux pog.elts.size #[] (by rw [add_comm]; rfl)
where
  aux : (n : Nat) → (A : Array Rat) → (pog.elts.size = A.size + n) →
        { A : Array Rat // A.size = pog.elts.size }
  | 0, A, h => ⟨A, h.symm⟩
  | n + 1, A, h =>
    have ASizeLt : A.size < pog.elts.size := by
      rw [h, ←add_assoc]; exact lt_succ_of_le (le_add_right _ _)
    let nextElt : Rat :=
      match pog.elts[A.size]'ASizeLt, pog.wf ⟨A.size, ASizeLt⟩, pog.inv ⟨A.size, ASizeLt⟩ with
        | var x, _, _ => weight x
        | disj x left right, ⟨hleft, hright⟩, hinv =>
          have := lt_aux hleft hinv
          have := lt_aux hright hinv
          let lmodels :=
            if left.polarity then A[left.var.natPred] else 1 - A[left.var.natPred]
          let rmodels :=
            if right.polarity then A[right.var.natPred] else 1 - A[right.var.natPred]
          lmodels + rmodels
        | conj n args, hwf, hinv =>
          conjProdW fun (j : Fin args.size) =>
              have := lt_aux (hwf j) hinv
              if args[j].polarity then A[args[j].var.natPred] else 1 - A[args[j].var.natPred]
    aux n (A.push nextElt) (by rw [Array.size_push, h, add_assoc, add_comm 1])

def countWeight (pog : Pog) (weight : Var → Rat) (x : Var) : Rat :=
  if h : x.natPred < pog.elts.size then
    have : x.natPred < (pog.toCountWeightArray weight).1.size := by
      rwa [(pog.toCountWeightArray weight).2]
    (pog.toCountWeightArray weight).1[x.natPred]
  else
    PropForm.countWeight weight (ILit.mkPos x).toPropForm

theorem countWeight_foldr_conj (weight : Var → Rat) (φs : List (PropForm Var)) :
   PropForm.countWeight weight (List.foldr PropForm.conj PropForm.tr φs) =
      List.foldr (fun a b => a * b) 1
        (φs.map (PropForm.countWeight weight)) := by
  induction φs
  . simp [PropForm.countWeight]
  . next φ φs ih =>
    rw [List.foldr_cons, PropForm.countWeight, ih, List.map, List.foldr]

theorem toCountWeightArray_spec (pog : Pog) (weight : Var → Rat) :
  ∀ i : Fin (pog.toCountWeightArray weight).1.size,
      (pog.toCountWeightArray weight).1[i] =
        PropForm.countWeight weight (pog.toPropForm (.mkPos (succPNat i))) := by
  apply aux
  rintro ⟨i, h⟩; contradiction
where
  aux : (n : Nat) → (A : Array Rat) → (h : pog.elts.size = A.size + n) →
          (h' : (∀ i : Fin A.size, A[i] =
            PropForm.countWeight weight (pog.toPropForm (.mkPos (succPNat i))))) →
    ∀ i : Fin (Pog.toCountWeightArray.aux pog weight n A h).1.size,
      (Pog.toCountWeightArray.aux pog weight n A h).1[i] =
        PropForm.countWeight weight (pog.toPropForm (.mkPos (succPNat i)))
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
        rw [toPropForm_aux_eq, heq, PropForm.countWeight]
      . next x left right hleft hright hinv heq _ _ =>
        rw [toPropForm]
        simp only [ILit.var_mkPos, natPred_succPNat, PropForm.withPolarity_mkPos, dif_pos ASizeLt]
        have hleft : PNat.natPred (ILit.var left) < A.size := by
          dsimp at hinv; rwa [hinv, PNat.natPred_lt_natPred]
        have hright : PNat.natPred (ILit.var right) < A.size := by
          dsimp at hinv; rwa [hinv, PNat.natPred_lt_natPred]
        have hl := h' ⟨_, hleft⟩; dsimp at hl; rw [hl]
        have hr := h' ⟨_, hright⟩; dsimp at hr; rw [hr]
        rw [toPropForm_aux_eq, heq, PropForm.countWeight, PNat.succPNat_natPred,
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
              PropForm.countWeight]
        . next hlnp =>
          rw [Bool.not_eq_true] at hlnp
          rw [ILit.mkPos_var_false _ hlnp, pog.toPropForm_of_polarity_eq_false _ hlnp,
              PropForm.countWeight]
          split
          . next hrp =>
            rw [ILit.mkPos_var_true _ hrp]
          . next hrnp =>
            rw [Bool.not_eq_true] at hrnp
            rw [ILit.mkPos_var_false _ hrnp, pog.toPropForm_of_polarity_eq_false _ hrnp,
              PropForm.countWeight]
      . next x args hwf hinv heq _ _ =>
        rw [toPropForm]
        simp only [ILit.var_mkPos, natPred_succPNat, PropForm.withPolarity_mkPos, dif_pos ASizeLt]
        rw [toPropForm_aux_eq, heq]; dsimp
        rw [conjProdW_eq_conjProdW', conjProdW', PropForm.arrayConj, PropForm.listConj,
          countWeight_foldr_conj]
        apply congr_arg
        rw [←Array.toList_eq, ←List.ofFn, List.map_ofFn]
        apply congr_arg
        apply funext; intro j
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
              PropForm.countWeight]

theorem countWeight_eq_countWeight (pog : Pog) (weight : Var → Rat) (x : Var) :
    pog.countWeight weight x = (pog.toPropForm (.mkPos x)).countWeight weight := by
  rw [countWeight, toPropForm, ILit.var_mkPos]
  split
  . next h =>
    have h' := h; rw [←(pog.toCountWeightArray weight).2] at h'
    have := pog.toCountWeightArray_spec weight ⟨_, h'⟩
    dsimp at this; rw [PNat.succPNat_natPred] at this
    dsimp; rw [this, toPropForm, ILit.var_mkPos, dif_pos h]
  . next h => rfl

theorem countWeight_eq' (pog : Pog) (weight : Var → Rat) (x : Var) (φ : PropForm Var) :
    pog.toPropForm (.mkPos x) = φ →
    pog.countWeight weight x = φ.countWeight weight := by
      intro h; rw [←h, countWeight_eq_countWeight]

end Pog
