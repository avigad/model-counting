import Mathlib.Data.Finset.Basic

import ProofChecker.Data.HashMap.Extra

def HashSet (α : Type) [BEq α] [Hashable α] := HashMap α Unit

namespace HashSet

variable {α : Type} [BEq α] [Hashable α]

def empty (α : Type) [BEq α] [Hashable α] : HashSet α :=
  HashMap.empty

def isEmpty (s : HashSet α) : Bool :=
  HashMap.isEmpty s

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

variable [DecidableEq α]

def toFinset (s : HashSet α) : Finset α :=
  HashMap.fold (init := ∅) (fun s a _ => s ∪ {a}) s

variable [LawfulBEq α] [HashMap.LawfulHashable α]

theorem mem_toFinset (s : HashSet α) (a : α) : a ∈ s.toFinset ↔ s.contains a := by
  sorry

theorem not_mem_toFinset (s : HashSet α) (a : α) : a ∉ s.toFinset ↔ ¬s.contains a := by
  simp [mem_toFinset]

@[simp]
theorem toFinset_empty : toFinset (empty α) = ∅ := by
  ext
  simp [mem_toFinset, empty, contains, HashMap.contains_empty]

@[simp]
theorem toFinset_insert (s : HashSet α) (a : α) :
    toFinset (s.insert a) = Insert.insert a s.toFinset := by
  ext
  simp [mem_toFinset, insert, contains, HashMap.contains_insert]
  tauto

@[simp]
theorem toFinset_singleton (a : α) : toFinset (singleton a) = {a} := by
  simp [singleton, toFinset_insert]

theorem toFinset_union_sub (s t : HashSet α) : (s.union t).toFinset ⊆ s.toFinset ∪ t.toFinset := by
  dsimp [union]
  intro x
  apply HashMap.foldRecOn
    (C := fun (acc : HashSet α) => x ∈ acc.toFinset → x ∈ s.toFinset ∪ t.toFinset)
    (hInit := by simp; tauto)
  intro _ a _ _ hFind
  have : a ∈ t.toFinset := by
    have := HashMap.contains_iff _ _|>.mpr ⟨_, hFind⟩
    simp [mem_toFinset, contains, this]
  aesop

theorem sub_toFinset_union_left (s t : HashSet α) : s.toFinset ⊆ (s.union t).toFinset := by
  dsimp [union]
  intro x
  apply HashMap.foldRecOn
    (C := fun (acc : HashSet α) => x ∈ s.toFinset → x ∈ acc.toFinset)
    (hInit := id)
  aesop

theorem sub_toFinset_union (s t : HashSet α) : s.toFinset ∪ t.toFinset ⊆ (s.union t).toFinset := by
  apply Finset.union_subset (sub_toFinset_union_left s t)
  dsimp [union]
  intro _ h
  have ⟨_, hFind⟩ := HashMap.contains_iff _ _|>.mp (mem_toFinset _ _ |>.mp h)
  have ⟨_, h⟩ := HashMap.fold_of_mapsTo_of_comm t (init := s) (fun acc a _ => acc.insert a)
    hFind (by intros; apply HashMap.insert_comm)
  simp [h]

@[simp]
theorem toFinset_union (s t : HashSet α) : (s.union t).toFinset = s.toFinset ∪ t.toFinset :=
  subset_antisymm (toFinset_union_sub s t) (sub_toFinset_union s t)

theorem toFinset_inter_sub (s t : HashSet α) : (s.inter t).toFinset ⊆ s.toFinset ∩ t.toFinset := by
  dsimp [inter]
  intro x
  apply HashMap.foldRecOn
    (C := fun (acc : HashSet α) => x ∈ acc.toFinset → x ∈ s.toFinset ∩ t.toFinset)
    (hInit := by simp)
  intro _ a _ _ hFind
  have : a ∈ t.toFinset := by
    have := HashMap.contains_iff _ _|>.mpr ⟨_, hFind⟩
    simp [mem_toFinset, contains, this]
  split <;>
    aesop (add norm mem_toFinset)

theorem sub_toFinset_inter (s t : HashSet α) : s.toFinset ∩ t.toFinset ⊆ (s.inter t).toFinset := by
  intro x
  simp only [inter, Finset.mem_inter]
  intro ⟨hS, hT⟩
  have ⟨_, hFind⟩ := HashMap.contains_iff _ _|>.mp (mem_toFinset _ _ |>.mp hT)
  have ⟨_, h⟩ := HashMap.fold_of_mapsTo_of_comm t (init := empty α)
    (fun acc a _ => if s.contains a then acc.insert a else acc)
    hFind ?comm
  case comm =>
    intros
    dsimp [insert]
    split_ifs <;>
      aesop (add norm HashMap.insert_comm)
  rw [h]
  split
  . simp
  . have : x ∉ s.toFinset :=
      not_mem_toFinset _ _ |>.mpr (by assumption)
    contradiction

@[simp]
theorem toFinset_inter (s t : HashSet α) : (s.inter t).toFinset = s.toFinset ∩ t.toFinset :=
  subset_antisymm (toFinset_inter_sub s t) (sub_toFinset_inter s t)

def Union (l : Array (HashSet α)) : HashSet α :=
  l.foldl (init := empty α) union

theorem toFinset_Union (l : Array (HashSet α)) :
    toFinset (Union l) = l.foldl (init := ∅) fun acc s => acc ∪ s.toFinset := by
  have : ∀ t, toFinset (l.foldl (init := t) union) =
      l.foldl (init := t.toFinset) fun acc s => acc ∪ s.toFinset := by
    simp only [Array.foldl_eq_foldl_data]
    induction l.data <;> simp_all
  simp [Union, this]

/-- Calculate the union of an array of `HashSet`s, and check if the array elements are all pairwise
disjoint. Return `(⋃ ss, true)` if array elements are pairwise disjoint, otherwise `(⋃ ss, false)`.
-/
def disjointUnion (ss : Array (HashSet α)) : HashSet α × Bool :=
  ss.foldl
    (init := (.empty α, true))
    fun (acc : HashSet α × Bool) t =>
      (acc.1.union t, acc.2 && (acc.1.inter t).isEmpty)

theorem mem_disjointUnion (ss : Array (HashSet α)) (a : α) :
    a ∈ (disjointUnion ss).fst.toFinset ↔ ∃ s ∈ ss.data, a ∈ s.toFinset := by
  sorry

theorem disjoint_disjointUnion (ss : Array (HashSet α)) : (disjointUnion ss).snd →
    ∀ (i j : Fin ss.size), i ≠ j → (ss[i]).toFinset ∩ (ss[j]).toFinset = ∅ := by
  sorry

end HashSet
