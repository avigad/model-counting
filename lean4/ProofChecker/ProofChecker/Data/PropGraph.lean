/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Linarith

import ProofChecker.Data.HashMap.Extra
import ProofChecker.Model.PropForm

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

instance [ToString α] : ToString (DagException α) where
  toString := fun
    | .alreadyExists a => s!"node '{a}' already exists"
    | .hasParents a ps => s!"node '{a}' cannot be deleted because it has incoming edges '{ps}'"
    | .invalidIndex a => s!"no node is indexed by '{a}'"

variable [BEq α] [Hashable α]

namespace Imp

def empty : Imp α β γ where
  nodes := .empty

def addNode (G : Imp α β γ) (a : α) (label : β) : Except (DagException α) (Imp α β γ) := do
  if G.nodes.contains a then
    throw <| .alreadyExists a
  return { G with
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

--  A-->|text|B
/-
def Dag.toMermaidChart [ToString ν] [ToString β] (g : Graph ν β) : String := Id.run do
  let mut ret := "flowchart TB\n"
  let mkArrowEnd (x : β) := if 0 ≤ b then s!"{x.var}" else s!"|NOT|{x.var}"
  for (x, node) in g.nodes.toArray do
    match node with
    | .sum a b =>
      ret := ret ++ s!"{x}([{x} OR])\n"
      ret := ret ++ s!"{x} -->{mkArrowEnd a}\n"
      ret := ret ++ s!"{x} -->{mkArrowEnd b}\n"
    | .prod ls =>
      ret := ret ++ s!"{x}({x} AND)\n"
      for l in ls do
        ret := ret ++ s!"{x} -->{mkArrowEnd l}\n"
  return ret
-/

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

/-- A node `a` with an out-edge `a ↦ b` exists in `G`. -/
def hasOutEdge (G : Imp α β γ) (a b : α) : Prop :=
  ∃ n l, G.nodes.mapsTo a n ∧ (l, b) ∈ n.outEdges

/-- A node `b` with an in-edge `a ↦ b` exists in `G`.
In any well-formed graph this should be equivalent to `hasOutEdge`. -/
def hasInEdge (G : Imp α β γ) (a b : α) : Prop :=
  ∃ n, G.nodes.mapsTo b n ∧ a ∈ n.inEdges

/-- The DAG `G` is well-formed. -/
structure WF (G : Imp α β γ) : Prop where
  -- NB: If this causes any difficulty, it *can be removed* just to support `addParent`
  edges_match : ∀ ⦃a b⦄, G.hasOutEdge a b ↔ G.hasInEdge a b
  acc_outEdge : ∀ ⦃a⦄, G.nodes.contains a → Acc (flip G.hasOutEdge) a

theorem WF.inEdge_closed_left {G : Imp α β γ} (H : G.WF) : G.hasInEdge a b →
    G.nodes.contains a := by
  intro h
  have ⟨n, _, hA, _⟩ := H.edges_match.mpr h
  exact G.nodes.contains_iff_mapsTo.mpr ⟨n, hA⟩

theorem WF.outEdge_closed_left {G : Imp α β γ} (H : G.WF) : G.hasOutEdge a b →
    G.nodes.contains a := by
  intro ⟨_, _, h, _⟩
  exact G.nodes.contains_iff_mapsTo.mpr ⟨_, h⟩

theorem WF.outEdge_closed_right {G : Imp α β γ} (H : G.WF) : G.hasOutEdge a b →
    G.nodes.contains b := by
  intro h
  have ⟨n, hA, _⟩ := H.edges_match.mp h
  exact G.nodes.contains_iff_mapsTo.mpr ⟨n, hA⟩

/-- Any index `a : α` is accessible because either it is accessible, or it's not in the graph. -/
theorem WF.acc_outEdge' {G : Imp α β γ} (H : G.WF) : ∀ a, Acc (flip G.hasOutEdge) a := by
  intro a
  by_cases h : G.nodes.contains a
  . exact H.acc_outEdge h 
  . exact Acc.intro a fun y hY => False.elim (h <| H.outEdge_closed_left hY)

theorem empty_WF : (@Imp.empty α _ _ β γ).WF where
  edges_match := by simp [hasInEdge, hasOutEdge, empty]
  acc_outEdge _ h := by simp [empty] at h

theorem addNode_WF {G G' : Imp α β γ} (H : G.WF) (a : α) (label : β)
    (hOk : G.addNode a label = .ok G') : G'.WF where
  edges_match := sorry
  acc_outEdge := sorry

-- TODO: Important well-formedness theorem
theorem addParent_WF {G G' : Imp α β γ} (H : G.WF) (a : α) (label : β) (children : List (γ × α))
    (hOk : G.addParent a l cs = .ok G') : G'.WF where
  edges_match a b := sorry
  acc_outEdge _ h := .intro _ (by
    intro b hIn
    sorry)

/-! Recursors. -/

-- praise the Mario
def ofAcc {r : β → β → Prop} (F : α → {x : β // Acc r x}) : WellFoundedRelation α :=
  invImage F ⟨InvImage r (·.1), ⟨fun ⟨_, h⟩ => InvImage.accessible _ h⟩⟩

/-- Non-caching recursive node fold. -/
def mapNode (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ)
    (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) : σ :=
  let cs : List (γ × σ) := n.outEdges.mapDep fun (a₂Label, a₂) h₂ =>
    have hEdge : G.hasOutEdge a a₂ :=
      ⟨n, a₂Label, h, h₂⟩
    match hFind : G.nodes.find? a₂ with
    | some n₂ => (a₂Label, G.mapNode H f a₂ n₂ hFind)
    | none    => False.elim (by
      have hContains := H.outEdge_closed_right hEdge
      apply G.nodes.find?_ne_none_of_contains hContains hFind)
  f a n.label cs
termination_by' mapNode => ofAcc fun ⟨a, _, _⟩ => ⟨a, H.acc_outEdge' a⟩

def nodeToTree (G : Imp α β γ) (H : G.WF) (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) :
    Tree α β γ :=
  G.mapNode H (fun a b cs => .node a b cs) a n h

-- Correctness theorem for recursive fold.
theorem mapNode_eq (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ)
    (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) :
    G.mapNode H f a n h = (G.nodeToTree H a n h).recOnNonDep f := by
  -- Recursive step
  have : ∀ (a₂ n₂) (hFind : G.nodes.find? a₂ = some n₂), G.hasOutEdge a a₂ →
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
  next hFind =>
    exfalso
    have hEdge : G.hasOutEdge a a₂ :=
      ⟨n, a₂Label, h, h₂⟩
    have hContains := H.outEdge_closed_right hEdge
    apply G.nodes.find?_ne_none_of_contains hContains hFind
termination_by' mapNode_eq => ofAcc fun ⟨a, _, _⟩ => ⟨a, H.acc_outEdge' a⟩

def recNonDep? (G : Imp α β γ) (H : G.WF) (start : α) (f : α → β → List (γ × σ) → σ) : Option σ :=
  match hFind : G.nodes.find? start with
  | some n => some (G.mapNode H f start n hFind)
  | none   => none

def mapNodeCached (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ) (cache : HashMap α σ) 
    (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) : HashMap α σ × σ :=
  match cache.find? a with
  | some v => (cache, v)
  | none =>
    let (cache', cs) : HashMap α σ × List (γ × σ) := n.outEdges.foldlDep
      (init := (cache, []))
      fun (cache, acc) (a₂Label, a₂) h₂ =>
        have hEdge : G.hasOutEdge a a₂ :=
          ⟨n, a₂Label, h, h₂⟩
        match hFind : G.nodes.find? a₂ with
        | some n₂ =>
          let (cache', val) := G.mapNodeCached H f cache a₂ n₂ hFind
          (cache', (a₂Label, val) :: acc)
        | none    => False.elim (by
          have hContains := H.outEdge_closed_right hEdge
          apply G.nodes.find?_ne_none_of_contains hContains hFind)
    (cache', f a n.label cs)
termination_by' mapNodeCached => ofAcc fun ⟨_, a, _, _⟩ => ⟨a, H.acc_outEdge' a⟩

def mapNodeCached_eq (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ)
    (cache : HashMap α σ) (hCache : ∀ a n h s, cache.find? a = some s → G.mapNode H f a n h = s)
    (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) :
    (G.mapNodeCached H f cache a n h).snd = G.mapNode H f a n h := by
  unfold mapNodeCached; split
  next hFind => rw [hCache a n h _ hFind]
  next hFind =>
    -- TODO: Will need some reasoning about List.foldlDep and List.map
    sorry

def mapNodeCachedTL (G : Imp α β γ) (H : G.WF) (f : α → β → List (γ × σ) → σ)
    (a : α) (n : DagNode α β γ) (h : G.nodes.mapsTo a n) : σ :=
  G.mapNodeCached H f .empty a n h |>.snd

@[csimp]
theorem mapNode_eq_mapNodeCachedTL : @mapNode = @mapNodeCachedTL := by
  unfold mapNodeCachedTL
  conv in mapNodeCached _ _ _ _ _ _ _ |>.snd =>
    rw [mapNodeCached_eq _ _ _ _ (fun _ _ _ _ h => (by rw [HashMap.find?_empty] at h; cases h))] 

/-! TODO: Change of model under operations. -/

theorem toModel_addNode : True := sorry

theorem toModel_addParent : True := sorry

/-! TODO: Conclusions about how recursion proceeds after operations given change of model. -/

end Imp

/-- A directed, acyclic graph. Nodes are indexed by `α` and this determines their identity via
`BEq α`. Nodes are also labeled with `β` and edges with `γ` which can be used to store additional
data.

It is designed for FBIP mutation with efficient node/edge insertion and removal. -/
def _root_.Dag (α : Type u) (β : Type v) (γ : Type w) [BEq α] [Hashable α] := {G : Imp α β γ // G.WF}

def empty : Dag α β γ :=
  ⟨Imp.empty, Imp.empty_WF⟩

def addNode (G : Dag α β γ) (a : α) (label : β) : Except (DagException α) (Dag α β γ) :=
  -- The exception effect and dependency don't compose nicely :(
  match h : G.val.addNode a label with
  | .error e => .error e
  | .ok v => .ok ⟨v, Imp.addNode_WF G.property a label h⟩

def addParent (G : Dag α β γ) (a : α) (label : β) (children : List (γ × α)) :
    Except (DagException α) (Dag α β γ) :=
  match h : G.val.addParent a label children with
  | .error e => .error e
  | .ok v => .ok ⟨v, Imp.addParent_WF G.property a label children h⟩

def recNonDep? (G : Dag α β γ) (start : α) (f : α → β → List (γ × σ) → σ) : Option σ :=
  G.val.recNonDep? G.property start f

end Dag

/-! Propositional DAGs. -/

inductive PropDag.Node where
  | conj
  | disj
  | var

/-- A propositional DAG is a forest of propositional formulas represented as shared graphs. -/
def PropDag (ν : Type) [BEq ν] [Hashable ν] := Dag ν PropDag.Node Bool

namespace PropDag

variable [BEq ν] [Hashable ν]

def empty : PropDag ν :=
  .empty

def addConj (G : PropDag ν) (x : ν) (children : List (Bool × ν)) :
    Except (Dag.DagException ν) (PropDag ν) :=
  G.addParent x .conj children

def addDisj (G : PropDag ν) (x : ν) (children : List (Bool × ν)) :
    Except (Dag.DagException ν) (PropDag ν) :=
  G.addParent x .disj children

def addVar (G : PropDag ν) (x : ν) : Except (Dag.DagException ν) (PropDag ν) :=
  G.addNode x .var

def count (G : PropDag ν) (x : ν) (nvars : Nat) : Option Nat :=
  G.recNonDep? x fun _ b cs =>
    match b with
    | .var => 2^(nvars - 1)
    | .conj => cs.foldl (init := 2^nvars) fun acc (neg, c) =>
      let c' := if neg then 2^nvars - c else c
      acc * c' / 2^nvars
    | .disj => cs.foldl (init := 0) fun acc (neg, c) =>
      let c' := if neg then 2^nvars - c else c
      acc + c'

/-- Return the formula corresponding to `x` in the POG, or simply `var x` if `x` is not in the POG.
-/
def toPropForm (G : PropDag ν) (x : ν) : PropForm ν :=
  let ret := G.recNonDep? x fun a b cs =>
    match b with
    | .var => .var a
    | .conj => cs.foldl (init := .tr) fun acc (neg, φ) =>
      let φ' := if neg then .neg φ else φ
      .conj acc φ'
    | .disj => cs.foldl (init := .fls) fun acc (neg, φ) =>
      let φ' := if neg then .neg φ else φ
      .disj acc φ'
  ret.getD (.var x)
  
instance : Inhabited (PropDag Nat) := ⟨.empty⟩

end PropDag

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
