import ProofChecker.Model.PropForm
import ProofChecker.Model.PropVars
import ProofChecker.Model.Cnf
import ProofChecker.Data.HashMap.Extra
import ProofChecker.Data.ICnf

/-! Clause database together with some (TBD provably correct) methods. For example, we can conclude
that if a clause follows from the current database by unit propagation, then it is implied by the
database's interpretation as a propositional formula. -/

/-- A stateful clause database, i.e. a dynamically modifiable CNF, for use in poly-time proof
checkers such as for LRAT. It uses in-place data structures, so should be used linearly.

(Persistent structures do not seem immediately helpful as linear formats do not backtrack.)

In `ClauseDb α`, `α` is the type of clause indices. -/
structure ClauseDb (α : Type) [BEq α] [Hashable α] where
  /-- Each clause is stored together with a flag indicating whether it has been deleted.
  Deleted clauses are logically not in the database. -/
  clauses : HashMap α (IClause × Bool) := {}

namespace HashMap

variable [BEq α] [Hashable α]

def mapOne (m : HashMap α β) (idx : α) (f : β → β) : HashMap α β :=
  match m.find? idx with
  | some b => m.insert idx (f b)
  | none => m

end HashMap

inductive UnitPropResult (α : Type) where
  | contradiction
  /-- The hint did not become unit. -/
  | hintNotUnit (hint : α)
  /-- The hint points at a nonexistent clause. -/
  | hintNonexistent (hint : α)
  | extended (τ : PartPropAssignment)

namespace UnitPropResult

def isContradiction (r : UnitPropResult α) : Bool :=
  r matches contradiction

end UnitPropResult

namespace ClauseDb

variable {α : Type} [BEq α] [Hashable α]

instance [ToString α] : ToString (ClauseDb α) where
  toString db := toString db.clauses.toList

def empty : ClauseDb α := { clauses := .empty }

def fold (db : ClauseDb α) (f : β → α → IClause → β) (init : β) : β :=
  db.clauses.fold (init := init) fun acc idx (C, deleted) =>
    if deleted then acc else f acc idx C

def foldM [Monad m] (db : ClauseDb α) (f : β → α → IClause → m β) (init : β) : m β :=
  db.clauses.foldM (init := init) fun acc idx (C, deleted) =>
    if deleted then pure acc else f acc idx C

def addClause (db : ClauseDb α) (idx : α) (C : IClause) : ClauseDb α :=
  { db with clauses := db.clauses.insert idx (C, false) }

def delClause (db : ClauseDb α) (idx : α) : ClauseDb α :=
  { db with clauses := db.clauses.mapOne idx fun (C, _) => (C, true) }

def getClause (db : ClauseDb α) (idx : α) : Option IClause :=
  db.clauses.find? idx |>.bind (fun (C, deleted) => if deleted then none else C) 

def contains (db : ClauseDb α) (idx : α) : Bool :=
  db.getClause idx |>.isSome

/-- Propagates units starting from the given assignment. The clauses in `hints` are expected to become
unit in the order provided. Returns the extended assignment, or `none` if a contradiction was found. -/
def unitPropWithHints (db : ClauseDb α) (τ : PartPropAssignment) (hints : Array α)
    : UnitPropResult α := Id.run do
  let mut τ := τ
  for hint in hints do
    let some C := db.getClause hint
      | return .hintNonexistent hint
    match C.reduce τ with
    | some #[u] => τ := τ.insert u.var u.polarity
    | some #[] => return .contradiction
    | _ => return .hintNotUnit hint
  return .extended τ
  
/-! Theorems about `ClauseDb` -/
  
def toPropTerm (db : ClauseDb α) : PropTerm Nat :=
  db.fold (init := .tr) fun acc _ C => acc.conj C.toPropTerm

theorem toPropTerm_getClause (db : ClauseDb α) (idx : α) :
    db.getClause idx = some C → db.toPropTerm.entails C.toPropTerm :=
  sorry

theorem toPropTerm_addClause (db : ClauseDb α) (idx : α) (C : IClause)
    -- only true when idx ∉ db
    : (db.addClause idx C).toPropTerm = db.toPropTerm.conj C.toPropTerm :=
  sorry

-- Not sure if true
theorem toPropTerm_delClause (db : ClauseDb α) (idx : α) :
    db.getClause idx = some C →
    (db.delClause idx).toPropTerm.conj C.toPropTerm = db.toPropTerm :=
  sorry

theorem entails_of_unitProp (db : ClauseDb α) (τ : PartPropAssignment) (hints : Array α) :
    db.unitPropWithHints τ hints |>.isContradiction → db.toPropTerm.entails (.neg τ.toPropTerm) :=
  sorry

end ClauseDb