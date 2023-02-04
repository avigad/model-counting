/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Linarith
import Mathlib.Data.Erased

import ProofChecker.Data.HashMap.Extra

/- ! Some utilities for using the order on `ℚ`. -/

def avg (a b : Rat) : Rat :=
  (a + b) / 2

theorem lt_avg_of_lt (a b : Rat) : a < b → a < avg a b :=
  fun h => calc
    a = (a + a) / 2 := by ring_nf; simp [mul_div_cancel a (by decide : (2 : ℚ) ≠ 0)]
    _ < (a + b) / 2 := div_lt_div_of_lt (by decide) (by linarith)
    _ = avg a b := rfl

theorem avg_lt_of_lt (a b : Rat) : a < b → avg a b < b :=
  fun h => calc
    avg a b = (a + b) / 2 := rfl
    _ < (b + b) / 2 := div_lt_div_of_lt (by decide) (by linarith)
    _ = b := by ring_nf; simp [mul_div_cancel a (by decide : (2 : ℚ) ≠ 0)]

/-! We define a data structure `Dag` for efficiently mutable directed acyclic graphs. -/

namespace Dag

structure DagNode (α : Type u) (β : Type v) (γ : Type w) where
  label : β
  inEdges : List α
  -- Convention: only out edges are labeled.
  outEdges : List (γ × α)

/-- Implementation of the `Dag` type. -/
structure Imp (α : Type u) (β : Type v) (γ : Type w) [BEq α] [Hashable α] where
  nodes : HashMap α (DagNode α β γ)

/-! Operations on DAGs. -/

/-- Ways in which operations on `Dag α _ _` can fail. -/
inductive DagException (α : Type u) where
  /-- There is no node indexed by `a`. -/
  | invalidIndex (a : α)
  /-- A node indexed by `a` cannot be added because one already exists. -/
  | alreadyExists (a : α)
  /-- The node indexed by `a` has incoming edges `ps`. -/
  | hasParents (a : α) (ps : List α)

variable [BEq α] [Hashable α]

namespace Imp

def empty : Imp α β γ where
  nodes := .empty

def addNode (G : Imp α β γ) (a : α) (label : β) : Imp α β γ :=
  { G with
    nodes := G.nodes.insert a {
      label
      inEdges := []
      outEdges := []
    }
  }

/-- Add a new node which has an outgoing edge to each of the `children`. -/
def addParent (G : Imp α β γ) (a : α) (label : β) (children : List (γ × α)) :
    Except (DagException α) (Imp α β γ) := do
  if G.nodes.contains a then
    throw <| .alreadyExists a
  -- TODO: how difficult is the `mut` to reason about?
  let mut G := G
  for (_, c) in children do
    if !G.nodes.contains c then
      throw <| .invalidIndex c
    G := { G with
      nodes := G.nodes.adjust c fun n => { n with inEdges := a :: n.inEdges } }
  return { G with
    nodes := G.nodes.insert a {
      label
      inEdges := []
      outEdges := children
    }
  }

/-- Delete a node and all its outgoing edges ensuring that it has no incoming edges. This is an
inverse to `addParent`. -/
def delParent (G : Imp α β γ) (a : α) : Except (DagException α) (Imp α β γ) := do
  let some n := G.nodes.find? a
    | throw <| .invalidIndex a
  if !n.inEdges.isEmpty then
    throw <| .hasParents a n.inEdges
  let mut G := G
  for (_, c) in n.outEdges do
    -- By well-formedness, this exception cannot actually occur.
    if !G.nodes.contains c then
      throw <| .invalidIndex c
    G := { G with
      nodes := G.nodes.adjust c fun n => { n with inEdges := n.inEdges.erase a } }
  return { G with nodes := G.nodes.erase a }

/- This is difficult to implement because checking for acyclicity requires doing a DFS in the worst
case. We know that a directed graph is acyclic iff a topological sort is possible. Suppose we keep
track of one such sort by storing a `depth` value at every node and ensure that if `A → B` is an
edge, `A.depth < B.depth` (for example, we could store all nodes in an ordered list and then the
index is the depth). Sadly, we cannot add edges and maintain the invariant locally just by moving
endpoints of the new edge. Consider the following graph, ordered as drawn (i.e. if `A` is to the
left of `B`, `A.depth < B.depth`)
 ┌───e───┐
 ▼       │
 D──►E ┌►C
     │ A──►B
     │     ▲
     └─────┘
and suppose we add the new edge `e`. The result is still a DAG (`A < C < D < E < B`) but validates
the `depth` invariant locally and it is not possible to fix just by moving the endpoints `C` and `D`
because `D < E < A < C`; so at least one of `E, A` must move.  Inventing some kind of local check
for cycles would be cool, except that it might be impossible. 

A directed graph G is acyclic iff DFS produces no back edges.
(Lemma 22.11 in Cormen, Leiserson, Rivest, Stein. "Introduction to Algorithms"). -/
-- def addEdge (G : Imp α β γ) (a₁ a₂ : α) (label : γ) : Except (DagException α) (Imp α β γ)

-- def delEdge (G : Imp α β γ) (a₁ a₂ : α) : Imp α β γ :=
--   { G with
--     nodes := G.nodes
--       |>.adjust a₁ (fun n =>
--         match n.outEdges.findIdx? (·.fst == a₂) with
--         | some i => { n with outEdges := n.outEdges.eraseIdx i }
--         | none => n)
--       |>.adjust a₂ (fun n => { n with inEdges := n.inEdges.erase a₁ })
--   }

end Imp

/-! The mathematical model of DAGs is a forest of trees (we don't prove anything about sharing
actually occuring, although it does). -/

inductive Tree (α : Type u) (β : Type v) (γ : Type w) where
  -- NOTE: The duplication of `idx`/`lbl` is redundant but matches the DAG structure more simply
  | node (idx : α) (lbl : β) (children : List (γ × Tree α β γ))

def Tree.recOnNonDep {γ motive : Type u} (t : Tree α β γ) (f : α → β → List (γ × motive) → motive) :
    motive :=
  let .node a b cs := t
  f a b (goEdges cs)
where
  goEdges : List (γ × Tree α β γ) → List (γ × motive)
    | []                     => []
    | (l, node a b cs) :: es => (l, f a b (goEdges cs)) :: goEdges es

theorem Tree.recOnNonDep_node {γ motive : Type u} (a : α) (b : β) (cs : List (γ × Tree α β γ))
    (f : α → β → List (γ × motive) → motive) :
    (node a b cs).recOnNonDep f = f a b (cs.map fun (l, c) => (l, c.recOnNonDep f)) := by
  conv => lhs; unfold recOnNonDep; simp_match; rw [goEdges]
where
  goEdges : (cs : List (γ × Tree α β γ)) →
      recOnNonDep.goEdges f cs = cs.map fun (l, c) => (l, c.recOnNonDep f)
    | [] => rfl
    | (l, node a b cs) :: es => by
      simp [recOnNonDep, recOnNonDep.goEdges, goEdges es]

/-! Reasoning about well-formedness of DAGs. -/

-- NOTE: `HashMap` lemmas hold more generally for `PartialEquivBEq α` but it's a lot more work to
-- reason with that and we don't need the generalization here so we just use `LawfulBEq α`. Note
-- that because the mathematical model assumes this, generalizing it would require changing the
-- basic definitions.
variable [LawfulBEq α]

namespace Imp

/-! Well-formedness invariants. -/

/-- An out-edge `a ↦ b` exists in `G`. -/
def hasOutEdge (G : Imp α β γ) (a b : α) : Prop :=
  ∃ n l, G.nodes.mapsTo a n ∧ (l, b) ∈ n.outEdges

/-- An in-edge `b ↤ a` (note flipped arguments) exists in `G`. In any well-formed graph this should
be equivalent to `hasOutEdge`. -/
def hasInEdge (G : Imp α β γ) (b a : α) : Prop :=
  ∃ n, G.nodes.mapsTo b n ∧ a ∈ n.inEdges

/-- The DAG `G` is well-formed. -/
structure WF (G : Imp α β γ) : Prop where
  inEdge_closed : ∀ {b a}, G.hasInEdge b a → G.nodes.contains a
  outEdge_closed : ∀ {a b}, G.hasOutEdge a b → G.nodes.contains b
  edges_match : ∀ a b, G.hasOutEdge a b ↔ G.hasInEdge b a
  acc_inEdge : ∀ {a}, G.nodes.contains a → Acc G.hasInEdge a

/-- Any index `a : α` is accessible because either it is accessible, or it's not in the graph. -/
theorem WF.acc_inEdge' {G : Imp α β γ} (H : G.WF) : ∀ a, Acc G.hasInEdge a := by
  intro a
  by_cases h : G.nodes.contains a
  . exact H.acc_inEdge h 
  . refine Acc.intro a fun y hY => ?_
    exfalso
    apply h (H.inEdge_closed hY)

theorem WF.acc_outEdge {G : Imp α β γ} (H : G.WF) : ∀ a, Acc (fun a b => G.hasOutEdge b a) a := by
  intro a
  conv => enter [1]; intro a b; rw [H.edges_match]
  exact H.acc_inEdge' a

/-! TODO: Correctness of operations. -/

theorem empty_WF : (@Imp.empty α _ _ β γ).WF where
  inEdge_closed h := sorry
  outEdge_closed h := sorry
  edges_match a b := sorry
  acc_inEdge a := sorry

/-! Recursors. -/

-- praise the Mario
def ofAcc {r : β → β → Prop} (F : α → {x : β // Acc r x}) : WellFoundedRelation α :=
  invImage F ⟨InvImage r (·.1), ⟨fun ⟨_, h⟩ => InvImage.accessible _ h⟩⟩

/-- Non-caching recursive node fold. -/
def mapNode (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ) (a : α) (n : DagNode α β γ)
    (h : G.nodes.mapsTo a n) : σ :=
  let cs : List (γ × σ) := n.outEdges.mapDep fun (a₂Label, a₂) h₂ =>
    have hEdge : G.hasInEdge a₂ a := by
      rw [← H.edges_match]
      exact ⟨n, a₂Label, h, h₂⟩
    match hFind : G.nodes.find? a₂ with
    | some n₂ => (a₂Label, G.mapNode H f a₂ n₂ hFind)
    | none    => False.elim (by
      have ⟨_, hN, _⟩ := hEdge
      apply G.nodes.find?_ne_none_of_mapsTo hN hFind)
  f a n.label cs
termination_by' mapNode => ofAcc fun ⟨a, _, _⟩ => ⟨a, H.acc_inEdge' a⟩

def nodeToTree (G : Imp α β γ) (H : G.WF) (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) :
    Tree α β γ :=
  G.mapNode H (fun a b cs => .node a b cs) a n h

-- Correctness theorem for recursive fold.
theorem mapNode_eq (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ) (a : α)
    (n : DagNode α β γ) (h : G.nodes.mapsTo a n) :
    G.mapNode H f a n h = (G.nodeToTree H a n h).recOnNonDep f := by
  -- Recursive step
  have : ∀ (a₂ n₂) (hFind : G.nodes.find? a₂ = some n₂), G.hasInEdge a₂ a →
      G.mapNode H f a₂ n₂ hFind = (G.nodeToTree H a₂ n₂ hFind).recOnNonDep f :=
    fun a₂ n₂ hFind _ => mapNode_eq G H f a₂ n₂ hFind
  unfold mapNode
  conv => lhs; pattern G.mapNode H f ..; rw [this _ _ _ hEdge]

  -- Decomposing and matching up expressions
  conv => rhs; unfold nodeToTree mapNode; pattern G.mapNode H ..; rw [← nodeToTree]
  rw [Tree.recOnNonDep_node, List.map_mapDep]
  dsimp
  congr 2
  funext (a₂Label, a₂) h₂
  split
  . simp
  next hNone =>
    exfalso
    have ⟨_, hN, _⟩ : G.hasInEdge a₂ a := by
      rw [← H.edges_match]
      exact ⟨n, a₂Label, h, h₂⟩
    apply G.nodes.find?_ne_none_of_mapsTo hN hNone
termination_by' mapNode_eq => ofAcc fun ⟨a, _, _⟩ => ⟨a, H.acc_inEdge' a⟩

def recNonDep? (G : Imp α β γ) (H : G.WF) (start : α) (f : α → β → List (γ × σ) → σ) : Option σ :=
  match hFind : G.nodes.find? start with
  | some n => some (G.mapNode H f start n hFind)
  | none   => none

/-- TODO: A caching recursor. -/
def recCachedNonDep (G : Imp α β γ) (H : G.WF) (start : α) (f : α → β → List (γ × σ) → σ) : Option σ :=
  sorry

-- TODO: The caching correctness theorem
theorem recCachedNonDep_eq (G : Imp α β γ) (H) (start) (f : α → β → List (γ × σ) → σ) :
  G.recCachedNonDep H start f = sorry := sorry

/-! TODO: Change of model under operations. -/

theorem toModel_addNode : True := sorry

theorem toModel_addParent : True := sorry

theorem toModel_delParent : True := sorry

/-! TODO: Conclusions about how recursion proceeds after operations. -/

end Imp

/-- A directed, acyclic graph. Nodes are indexed by `α` and this determines their identity via
`BEq α`. Nodes are also labeled with `β` and edges with `γ` which can be used to store additional
data.

It is designed for FBIP mutation with efficient node/edge insertion and removal. -/
def _root_.Dag (α : Type u) (β : Type v) (γ : Type w) [BEq α] [Hashable α] := {G : Imp α β γ // G.WF}

end Dag

/-! Propositional DAGs. -/

inductive PropDag.Node where
  | conj
  | disj
  | var

/-- A propositional DAG is a forest of propositional formulas represented as shared graphs. -/
def PropDag (ν : Type) [BEq ν] [Hashable ν] := Dag ν PropDag.Node Bool

def PropDag.count : Nat := sorry

def PropDag.toPropForm : Unit := sorry

#exit

-- This fold is not super useful for me in the end, I just need the recursors.
def fold {σ : Type} (G : Imp α β γ) (H : G.WF) (start : α) 
    (init : σ) (f : σ → α → β → γ → σ) : σ :=
  go ⟨start, H.acc_any start⟩ init
where go (start : {a : α // Acc G.hasInEdge a}) (acc : σ) :=
  match hFind : G.nodes.find? start.val with
  | some n =>
    n.outEdges.foldlDep (init := acc) fun acc (e, eLabel) h =>
      let acc' := f acc e n.label eLabel
      have : G.hasInEdge e start := sorry
      go ⟨e, H.acc_any e⟩ acc'
  | _ => acc
  termination_by' go => ofAcc fun ⟨a, _⟩ => a
