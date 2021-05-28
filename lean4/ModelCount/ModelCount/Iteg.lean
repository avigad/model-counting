import ModelCount.Lib

/- itegs-/

inductive IteElt
  | Tr                : IteElt 
  | Fls               : IteElt
  | Var (i : Nat)     : IteElt
  | Ite (c t f : Nat) : IteElt
deriving Repr

instance : Inhabited IteElt := ⟨IteElt.Tr⟩

open IteElt

/-- `IteEltBounded x b` says that if `x` is an ite clause, then the branches are less than `b`-/
def IteEltBounded : IteElt → Nat → Prop
  | Tr,        _ => True
  | Fls,       _ => True
  | Var i,     _ => True
  | Ite c t f, b => t < b ∧ f < b

-- No need to bound i, since the default value of an `IteElt` is `Tr` 
def Iteg := { I : Array IteElt // ∀ i, IteEltBounded I[i] i }

-- coerce to an array
instance itegCoe (n : Nat) : CoeHead Iteg (Array IteElt) where coe v := v.val

-- TODO: a hack to fix an annoying dependcy; find a better way
theorem match_aux (i : IteElt) (a b : α) (c : Nat → α) (d : Nat → Nat → Nat → α) :
    (match h:i with | Tr => a | Fls => b | Var j => c j | Ite c t f => d c t f) =
      (match i with | Tr => a | Fls => b | Var j => c j | Ite c t f => d c t f) := 
by cases i <;> rfl


/- semantics: the `eval` function -/

def Assignment : Type := Nat → Bool

namespace Iteg

def evalF (I : Iteg) (v : Assignment) (m : Nat) (eval_rec : (∀ i, i < m → Bool)) : Bool :=
  match h:I.val[m] with
    | Tr            => true
    | Fls           => false
    | Var k         => v k
    | Ite c t f     => 
        have bdd : IteEltBounded (Ite c t f) m by { rw ←h; apply I.property }
        cond (v c) (eval_rec _ bdd.1) (eval_rec _ bdd.2)


/-- `I.eval v j` evaluated line `j` of iteg `I` with assignment `v` -/
noncomputable def eval (I : Iteg) (v : Assignment) : Nat → Bool := 
WellFounded.fix Nat.ltWf (evalF I v)

theorem eval_eq (I : Iteg) (v : Assignment) (j : Nat) : 
  eval I v j = match I.val[j] with 
                 | Tr        => true
                 | Fls       => false
                 | Var k     => v k 
                 | Ite c t f => cond (v c) (eval I v t) (eval I v f) := 
by
  apply Eq.trans $ WellFounded.fixEq Nat.ltWf (evalF I v) j
  apply Eq.trans _ (match_aux _ _ _ _ _); rfl

@[simp] theorem eval_Tr {I : Iteg} {j : Nat} (h : I.val[j] = Tr) (v : Assignment)  :
  I.eval v j = true := by rw [eval_eq, h]
@[simp] theorem eval_Fls {I : Iteg} {j : Nat} (h : I.val[j] = Fls) (v : Assignment) :
  I.eval v j = false := by rw [eval_eq, h]
@[simp] theorem eval_Var {I : Iteg} {j k : Nat} (h : I.val[j] = Var k) (v : Assignment) :
  I.eval v j = v k := by rw [eval_eq, h]
@[simp] theorem eval_Ite {I : Iteg} {j c t f : Nat} (h : I.val[j] = Ite c t f) (v : Assignment) :
  I.eval v j = cond (v c) (I.eval v t) (I.eval v f) := by rw [eval_eq, h]

end Iteg

namespace Iteg
open Finset

/- the `vars` function -/

def varsF (I : Iteg) (m : Nat) (vars_rec : (∀ i, i < m → Finset Nat)) : Finset Nat :=
  match h:I.val[m] with
    | Tr            => ∅
    | Fls           => ∅
    | Var j         => singleton j
    | Ite c t f     =>
        have bdd : IteEltBounded (Ite c t f) m by { rw ←h; apply I.property }
        singleton c ∪ (vars_rec _ bdd.1) ∪ (vars_rec _ bdd.2)

/-- `I.vars j` returns the `Finset` of variables that line `j` iteg `I` depends on. -/
noncomputable def vars (I : Iteg) : Nat → Finset Nat := WellFounded.fix Nat.ltWf (varsF I)

theorem vars_eq (I : Iteg) (j : Nat) : 
  vars I j = match I.val[j] with 
               | Tr        => ∅
               | Fls       => ∅
               | Var k     => singleton k
               | Ite c t f => singleton c ∪ vars I t ∪ vars I f := 
by
  apply Eq.trans $ WellFounded.fixEq Nat.ltWf (varsF I) j
  apply Eq.trans _ (match_aux _ _ _ _ _); rfl

@[simp] theorem vars_Tr {I : Iteg} {j : Nat} (h : I.val[j] = Tr) :
  I.vars j = (∅ : Finset Nat) := by rw [vars_eq, h]
@[simp] theorem var_Fls {I : Iteg} {j : Nat} (h : I.val[j] = Fls) :
  I.vars j = (∅ : Finset Nat) := by rw [vars_eq, h]
@[simp] theorem vars_Var {I : Iteg} {j k : Nat} (h : I.val[j] = Var k) :
  I.vars j = singleton k := by rw [vars_eq, h]
@[simp] theorem vars_Ite {I : Iteg} {j c t f : Nat} (h : I.val[j] = Ite c t f) :
  I.vars j = singleton c ∪ I.vars t ∪ I.vars f := by rw [vars_eq, h]


/- the `count` function -/

def countF (I : Iteg) (numVars : Nat) (m : Nat) (count_rec : ∀ i, i < m → Nat) : Nat :=
  match h:I.val[m] with
    | Tr            => 2 ^ numVars
    | Fls           => 0
    | Var j         => 2 ^ (numVars - 1)
    | Ite c t f     =>
        have bdd : IteEltBounded (Ite c t f) m by { rw ←h; apply I.property }
        (count_rec _ bdd.1 + count_rec _ bdd.2) / 2

/-- 
`I.count I j` counts the number of models of line `j` of iteg `I`, assuming `numVars` variables in total.
-/
noncomputable def count (I : Iteg) (numVars : Nat) : Nat → Nat := 
WellFounded.fix Nat.ltWf (countF I numVars)

theorem count_eq (I : Iteg) (numVars : Nat) (j : Nat) : 
  count I numVars j = match I.val[j] with 
                        | Tr        => 2 ^ numVars
                        | Fls       => 0
                        | Var k     => 2 ^ (numVars - 1)
                        | Ite c t f => (count I numVars t + count I numVars f) / 2 := 
by
  apply Eq.trans $ WellFounded.fixEq Nat.ltWf (countF I numVars) j
  apply Eq.trans _ (match_aux _ _ _ _ _); rfl

@[simp] theorem count_Tr {I : Iteg} {j : Nat} (h : I.val[j] = Tr) (numVars : Nat) :
  I.count numVars j = 2 ^ numVars := by rw [count_eq, h]
@[simp] theorem count_Fls {I : Iteg} {j : Nat} (h : I.val[j] = Fls) (numVars : Nat) :
  I.count numVars j = 0 := by rw [count_eq, h]
@[simp] theorem count_Var {I : Iteg} {j k : Nat} (h : I.val[j] = Var k) (numVars : Nat) :
  I.count numVars j = 2 ^ (numVars - 1) := by rw [count_eq, h]
@[simp] theorem count_Ite {I : Iteg} {j c t f : Nat} (h : I.val[j] = Ite c t f) (numVars : Nat) :
  I.count numVars j = (count I numVars t + count I numVars f) / 2 := by rw [count_eq, h]


/- free itegs -/

def free (I : Iteg) : Prop := 
∀ j, match I.val[j] with
       | Tr => True
       | Fls => True
       | Var k => True
       | Ite c t f => c ∉ I.vars t ∧ c ∉ I.vars f


/- counting models assignments -/

def defined_on (v : Assignment) (s : Finset Nat) := ∀ n, ¬ n ∈ s → v n = false

theorem finite_defined_on (s : Finset Nat) : Set.finite (fun v : Assignment => defined_on v s) :=
sorry

def models (s : Finset Nat) : Finset Assignment := ⟨_, finite_defined_on s⟩

@[simp] theorem card_models (s : Finset Nat) : card (models s) = 2 ^ card s :=
sorry


/- auxiliary lemmas -/

theorem card_models_Var {s : Finset Nat} {k : Nat} (h : k ∈ s) : 
  card {v ∈ models s | v k = True} = 2 ^ (card s - 1) :=
sorry

/- this is the main combinatorial lemma behind the counting algorithm -/
theorem card_models_Ite {I : Iteg} {s : Finset Nat} {c : Nat} 
    (h₀ : c ∈ s) (h₁ : c ∉ I.vars t) (h₂ : c ∉ I.vars f) : 
  card {v ∈ models s | cond (v c) (eval I v t) (eval I v f) = true} =
    (card {v ∈ models s | eval I v t = true} + card {v ∈ models s | eval I v f = true}) / 2 := 
sorry


/- the main theorem -/

theorem card_models_Iteg (I : Iteg) (v : Assignment) (s : Finset Nat) (Ifree : free I): 
   ∀ j, I.vars j ⊆ s →  card {v ∈ models s | I.eval v j = true} = I.count (card s) j := 
by
  intro j
  induction j using Nat.CompleteInductionOn with
    | ind j ih =>
      rw count_eq
      cases h:I.val[j] with
      | Tr        => simp [h]
      | Fls       => simp [h]
      | Var k     =>
          simp [vars_Var h, eval_Var h]
          apply card_models_Var
      | Ite c t f => 
          have bdd : IteEltBounded (Ite c t f) j by { rw ←h; apply I.property }
          have _ := Ifree j
          rw h at this
          have free: c ∉ I.vars t ∧ c ∉ I.vars f from this
          simp [vars_Ite h, eval_Ite h]
          intro h'
          have h₀ : c ∈ s from singleton_subset.mp (subset_trans (subset_union_left _ _) h')
          have h₁ : vars I t ⊆ s from subset_trans (subset_union_left _ _) 
                                        (subset_trans (subset_union_right _ _) h')
          have h₂ : vars I f ⊆ s from subset_trans (subset_union_right _ _) 
                                        (subset_trans (subset_union_right _ _) h')
          have h₃ : card {v ∈ models s | I.eval v t = true} = count I (card s) t from ih _ bdd.1 h₁
          have h₄ : card {v ∈ models s | I.eval v f = true} = count I (card s) f from ih _ bdd.2 h₂
          rw [←h₃, ←h₄]
          apply card_models_Ite h₀ free.1 free.2


/- The array-based algorithm. -/

def countModelsStep (I : Array IteElt) (numVars : Nat) (i : Nat) (O : Array Nat) :=
  O.push $ match I[i] with
            | Tr         => 2 ^ numVars
            | Fls        => 0
            | Var k      => 2^ (numVars - 1)
            | Ite c t f  => (O[t] + O[f]) / 2

def countModels (I : Array IteElt) (numVars : Nat) : Array Nat := do 
  let mut O : Array Nat := #[]
  for i in [:I.size] do O := countModelsStep I numVars i O
  return O

/-
The array-based algorithm is equal to the recursive description.
-/

@[simp] theorem size_countModelsStep (I : Array IteElt) (numVars : Nat) (i : Nat) (O : Array Nat) :
    Array.size (countModelsStep I numVars i O) = O.size + 1 := by
  simp [countModelsStep]

@[simp] theorem get_countModelsStep_of_lt (I : Array IteElt) (numVars : Nat) (O : Array Nat) 
      (i j : Nat) (hi : i < O.size) :
    (countModelsStep I numVars j O)[i] = O[i] := by
  simp [countModelsStep]; rw [Array.get_push_of_lt O _ hi]

@[simp] theorem get_countModelsStep_size (I : Array IteElt) (numVars : Nat) (O : Array Nat) :
    (countModelsStep I numVars i O)[O.size] =
      match I[i] with
        | Tr         => 2 ^ numVars
        | Fls        => 0
        | Var k      => 2^ (numVars - 1)
        | Ite c t f  => (O[t] + O[f]) / 2 := by
  simp [countModelsStep]

def countModelsRec (I : Array IteElt) (numVars : Nat) (n j : Nat) (init : Array Nat) : Array Nat := 
  Std.Range.forIn.loop (m := Id) [:I.size]
    (fun i (O : Array Nat) => ForInStep.yield $ countModelsStep I numVars i O) n j init

theorem countModels_eq_countModelsRec (I : Array IteElt) (numVars : Nat) :
  countModels I numVars = countModelsRec I numVars I.size 0 #[] := rfl

theorem countModelsRecSucc (I : Array IteElt) (numVars : Nat) (n j : Nat) (init : Array Nat) : 
    countModelsRec I numVars (n + 1) j init =
      if j ≥ Array.size I then init else
        countModelsRec I numVars n (j + 1) (countModelsStep I numVars j init) := by
  simp [countModelsRec]

theorem countModelsRec_prop (I : Iteg) (numVars : Nat) : ∀ n j (init : Array Nat),
  init.size = j → (∀ i, i < j → init[i] = I.count numVars i) → n + j ≤ I.val.size →  
    let O := countModelsRec I.val numVars n j init
    O.size = n + j ∧ ∀ i, i < n + j → O[i] = I.count numVars i
| 0, j, init, h₁, h₂, _ => by
  simp [countModelsRec]
  exact ⟨h₁, fun i hi => h₂ _ hi⟩ 
| n+1, j, init, h₁, h₂, h₃ => by
  simp [countModelsRecSucc]
  let O := countModelsStep I.val numVars j init
  have h₄ : Array.size O = j + 1 by simp [h₁]
  have h₅ : ∀ i, i < j + 1 → O[i] = count I numVars i by
    intros i hi
    cases Nat.le_iff_lt_or_eq.mp $ Nat.lt_succ_iff_le.mp hi with
      | inl h' =>
        rw [←h₂ _ h', get_countModelsStep_of_lt]; try rfl
        rw [h₁]; apply h'
      | inr h' =>
        rw [h', ←h₁, get_countModelsStep_size, count_eq, h₁]
        cases ieq: I.val[j] with 
          | Ite c t f => 
            have bdd : IteEltBounded (Ite c t f) j by { rw ←ieq; apply I.property }
            simp [h₂ _ bdd.1, h₂ _ bdd.2]
          | _ => rfl
  have h₆ : n + (j + 1) = n + 1 + j by rw [Nat.add_assoc, Nat.add_comm j]
  have h₇ : n + (j + 1) ≤ I.val.size by rw [h₆]; exact h₃ 
  let ih := countModelsRec_prop I numVars n (j+1) (countModelsStep I.val numVars j init) h₄ h₅ h₇
  have h₇ : ¬ j ≥ I.val.size by
    apply Nat.not_le_of_lt
    apply Nat.lt_of_lt_of_le _ h₃
    rw [Nat.add_comm (n + 1), ←Nat.add_assoc]
    apply Nat.lt_succ_of_le
    apply Nat.le_add_right
  rw [ifNeg h₇, ←h₆]
  exact ih

theorem countModels_eq_count (I : Iteg) (numVars : Nat) {j} (hj : j < I.val.size) :
    (countModels I.val numVars)[j] = I.count numVars j :=
  (countModelsRec_prop I numVars I.val.size 0 #[] Array.size_empty 
    (fun _ hi => absurd hi (Nat.not_lt_zero _)) (Nat.le_refl _)).2 _ hj

end Iteg
