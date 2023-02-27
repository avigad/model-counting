import Mathlib.Data.Finset.Basic

import ProofChecker.Data.HashMap.Extra

def HashSet (α : Type) [BEq α] [Hashable α] := HashMap α Unit

namespace HashSet

variable {α : Type} [BEq α] [Hashable α]

def empty (α : Type) [BEq α] [Hashable α] : HashSet α :=
  HashMap.empty

def isEmpty (s : HashSet α) : Bool :=
  HashMap.isEmpty s

def size (s : HashSet α) : Nat :=
  HashMap.size s

def insert (s : HashSet α) (a : α) : HashSet α :=
  HashMap.insert s a ()

def singleton (a : α) : HashSet α :=
  empty α |>.insert a

def contains (s : HashSet α) (a : α) : Bool :=
  HashMap.contains s a

def union (s t : HashSet α) : HashSet α :=
  HashMap.fold (init := s) (fun acc a _ => acc.insert a) t

def inter (s t : HashSet α) : HashSet α :=
  HashMap.fold (init := empty α) (fun acc a _ =>
    if s.contains a then acc.insert a else acc) t
      
def fold (f : σ → α → σ) (init : σ) : HashSet α → σ :=
  HashMap.fold (init := init) (fun acc a _ => f acc a)

def foldM [Monad m] (f : σ → α → m σ) (init : σ) : HashSet α → m σ :=
  HashMap.foldM (init := init) (fun acc a _ => f acc a)

variable [DecidableEq α]

def toFinset (s : HashSet α) : Finset α :=
  HashMap.fold (init := ∅) (fun s a _ => s ∪ {a}) s
  
variable [LawfulBEq α] [HashMap.LawfulHashable α]

theorem toFinset_isEmpty {s : HashSet α} : s.isEmpty → s.toFinset = ∅ := by
  intro h
  sorry

theorem isEmpty_empty : isEmpty (empty α) := by
  sorry

@[simp]
theorem toFinset_empty : toFinset (empty α) = ∅ := by
  exact toFinset_isEmpty isEmpty_empty
  
@[simp]
theorem toFinset_insert (s : HashSet α) (a : α) : toFinset (s.insert a) = s.toFinset ∪ {a} := by
  sorry

@[simp]
theorem toFinset_singleton (a : α) : toFinset (singleton a) = {a} := by
  simp [singleton, toFinset_insert]

theorem contains_iff (s : HashSet α) (a : α) : s.contains a ↔ a ∈ s.toFinset := by
  sorry

theorem insert_comm (s : HashSet α) (a b : α) : (s.insert a).insert b = (s.insert b).insert a := by
  dsimp [insert]
  apply HashMap.insert_comm

@[simp]
theorem toFinset_union (s t : HashSet α) [LawfulBEq α]
    : toFinset (s.union t) = s.toFinset ∪ t.toFinset := by
  rw [union, HashMap.fold_eq_fold_toList _ _ _ (by simp [insert_comm])]
  sorry

@[simp]
theorem toFinset_inter (s t : HashSet α) : toFinset (s.inter t) = s.toFinset ∩ t.toFinset := by
  sorry

def Union (l : Array (HashSet α)) : HashSet α :=
  l.foldl (init := empty α) union

theorem toFinset_Union (l : Array (HashSet α)) :
    toFinset (Union l) = l.foldl (init := ∅) fun acc s => acc ∪ s.toFinset := by
  have : ∀ t, toFinset (l.foldl (init := t) union) =
      l.foldl (init := t.toFinset) fun acc s => acc ∪ s.toFinset := by
    simp only [Array.foldl_eq_foldl_data]
    induction l.data <;> simp_all
  simp [Union, this]

/-- Calculate the Union and also check if the elements are all pairwise disjoint. -/
def Union' (l : Array (HashSet α)) : HashSet α × Bool :=
  l.foldl
    (init := (.empty α, true))
    fun (acc : HashSet α × Bool) t =>
      (acc.1.union t, acc.2 && (acc.1.inter t).isEmpty)

@[simp]
theorem fst_Union' (l : Array (HashSet α)) : (Union' l).fst = Union l := by
  -- for another day..
  sorry

theorem snd_Union' (l : Array (HashSet α)) (h : Union' l |>.snd) :
    ∀ s ∈ l.data, ∀ t ∈ l.data, s ≠ t → s.toFinset ∩ t.toFinset = ∅ := by
  intro s hs t ht hNe
  -- for another day..
  sorry

end HashSet