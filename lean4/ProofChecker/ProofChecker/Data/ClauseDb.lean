import Std.Data.HashMap
import Lean

import ProofChecker.PropForm

/-! Clause database together with some (TBD provably correct) methods. For example, we can conclude
that if a clause follows from the current database by unit propagation, then it is implied by the
database's interpretation as a propositional formula. -/

/-- A stateful clause database, i.e. a dynamically modifiable CNF, for use in poly-time proof
checkers such as for LRAT. It uses in-place data structures, so should be used linearly.

(Persistent structures do not seem immediately helpful as linear formats do not backtrack.)

In `ClauseDb α β`, `α` is the type of clause indices and `β` is the type of literals.
Later on, we require `Neg β` for negating literals. -/
structure ClauseDb (α β : Type) [BEq α] [Hashable α] where
  clauses : Std.HashMap α (Array β × Bool) := {}
  -- LATER: which clauses a given literal occurs in.
  -- occurs : Std.HashMap β (Array α)

/-- A partial assignment to propositional literals. It assigns directly to literals, so it be
inconsistent. -/
-- TODO: is a lit-indexed Array Bool better?
def PartPropAssignment (β : Type) := List β

/-- Interpret the negation of a partial assignment as a clause. For example, x₁ ∧ -x₂ ↦ -x₁ ∨ x₂. -/
def PartPropAssignment.interpNeg [Neg β] (τ : PartPropAssignment β) : PropForm β :=
  -- TODO: how does consistency come in here? The negation must be well-behaved wrt evaluation;
  -- maybe; or maybe it will not end up mattering later if we relativize to neg
  τ.foldl (init := .fls) fun acc l => acc.disj (.var (-l))

def Clause.interp (C : Array β) : PropForm β :=
  C.foldl (init := .fls) fun acc l => acc.disj (.var l)

namespace Std.HashMap

variable [BEq α] [Hashable α]

def mapOne (m : HashMap α β) (idx : α) (f : β → β) : HashMap α β :=
  match m.find? idx with
  | some b => m.insert idx (f b)
  | none => m

end Std.HashMap

inductive UnitPropResult (α β : Type) where
  | contradiction
  /-- Either the hint did not become unit or it points at a nonexistent clause. -/
  | wrongHint (hint : α)
  | extended (τ : PartPropAssignment β)

namespace UnitPropResult

def isContradiction (r : UnitPropResult α β) : Bool :=
  r matches contradiction

end UnitPropResult

namespace ClauseDb

variable {α : Type} [BEq α] [Hashable α]

instance [ToString α] [ToString β] : ToString (ClauseDb α β) where
  toString db := toString db.clauses.toList

def empty : ClauseDb α β := { clauses := .empty }

-- Detail: `PropForm β` has literals as variables. This makes it possible
-- to write down inconsistent assignments x ↦ ⊤, -x ↦ ⊤. We'll just require
-- `LawfulNeg` or something like that.
def interp (db : ClauseDb α β) : PropForm β :=
  db.clauses.fold (init := .tr) fun acc _ (cl, deleted) =>
    if deleted then acc else acc.conj (Clause.interp cl)

def addClause (db : ClauseDb α β) (idx : α) (C : Array β) : ClauseDb α β :=
  { db with clauses := db.clauses.insert idx (C, false) }

def delClause (db : ClauseDb α β) (idx : α) : ClauseDb α β :=
  { db with clauses := db.clauses.mapOne idx fun (C, _) => (C, true) }

def getClause (db : ClauseDb α β) (idx : α) : Option (Array β) :=
  db.clauses.find? idx |>.bind (fun (C, deleted) => if deleted then none else C) 

def contains (db : ClauseDb α β) (idx : α) : Bool :=
  db.getClause idx |>.isSome

theorem interp_addClause (db : ClauseDb α β) (idx : α) (C : Array β)
    (h : db.clauses.contains idx = false)
    : (db.addClause idx C).interp = db.interp.conj (Clause.interp C) :=
  sorry

/-- Propagates units starting from the given assignment. The clauses in `hints` are expected to become
unit in the order provided. Returns the extended assignment, or `none` if a contradiction was found. -/
def unitPropWithHints [BEq β] [Neg β] (db : ClauseDb α β) (τ : PartPropAssignment β) (hints : Array α)
    : UnitPropResult α β := Id.run do
  let mut τ := τ
  for hint in hints do
    let some C := db.getClause hint
      | return .wrongHint hint
    match reduceClause C τ with
    | some [u] => τ := u :: τ
    | some [] => return .contradiction
    | _ => return .wrongHint hint
  return .extended τ
where
  /-- Reduces a clause by a partial assignment. Returns `none` if it became satisfied,
  otherwise `some C'` where `C'` is the reduced clause. -/
  reduceClause (C : Array β) (τ : PartPropAssignment β) : Option (List β) :=
    C.foldlM (init := []) fun acc l =>
      -- NOTE: linear in assignment size
      match τ.find? (fun l' => l' == l || l' == -l) with
      | none => l :: acc
      | some l' => if l' == l then none else acc

theorem entails_of_unitProp [BEq β] [Neg β] (db : ClauseDb α β) (τ : PartPropAssignment β)
    (hints : Array α) : db.unitPropWithHints τ hints |>.isContradiction → db.interp ⊨ τ.interpNeg :=
  sorry

end ClauseDb