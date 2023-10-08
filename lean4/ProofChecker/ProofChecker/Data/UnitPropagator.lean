import ProofChecker.Data.ICnf

/-! A unit propagation module.

Is it meant to be stored persistently and used linearly.

It uses a counter to avoid resetting partial assignments on every new UP sequence. -/

structure UnitPropagator where
  assignment : Array Int
  generation : Nat
  --h: 0 ≤ generation
  --h: ∀ x ∈ assignment, x ≤ generation

namespace UnitPropagator
  -- Note : maxVar is a ceiling on the number of variables that will *ever* be used
  def new (maxVar : Nat) : UnitPropagator where
    assignment := Array.mkArray maxVar 0
    generation := 1

  /-- Reset the variable assignment to the empty one. -/
  def newPropagation (p : UnitPropagator) : UnitPropagator :=
    { p with generation := p.generation + 1 }

  def setLit (p : UnitPropagator) (l : ILit) : UnitPropagator :=
    let v : Int := if l.polarity then p.generation else -p.generation
    { p with assignment := p.assignment.set! (l.var.val-1) v }

  /-- The value of the given literal in the current assignment, if assigned. -/
  def litValue? (p : UnitPropagator) (l : ILit) : Option Bool :=
    let v := p.assignment.getD (l.var.val-1) 0
    if v.natAbs == p.generation then
      some <| xor (v < 0) l.polarity
    else none

  -- check if the given clause is a tautology
  -- so this thing is more than a unit propagator; a general PartPropAssignment!
  def checkTauto (p : UnitPropagator) (C : IClause) : UnitPropagator × Bool := Id.run do
    let mut p := p.newPropagation
    for l in C do
      if let some false := p.litValue? l then
        return (p, true)
    return (p, false)
    
  /-- Extend the variable assignment by the negation of `C`, i.e.,
  set `l ↦ ⊥` for each `l ∈ C`.
  Nothing is checked, so this might override current assignments. -/
  -- NB: might be easier to verify if we make this always bump p.generation; it's only used at the start anyway
  def extendNegated (p : UnitPropagator) (C : IClause) : UnitPropagator :=
    C.foldl (init := p) (fun p l => p.setLit (-l))

  inductive PropagateResult where
    | extended
    | contradiction
    | notUnit

  /-- Extend the variable assignment `τ` by the clause `C`
    which is expected to become a unit w.r.t. the current assignment.
    If the clause contradicts the current assignment, `contradiction` is returned.
    If it's consistent but did not become a unit, `notUnit` is returned.
      This case includes clauses that were units to begin with, but the unit was already in the assignment.
      The unit must be 'new' w.r.t. the current assignment.
    If the result is not `extended`, the variable assignment afterwards is unspecified. -/
  def propagateUnit (p : UnitPropagator) (C : IClause) : UnitPropagator × PropagateResult := Id.run do
    let mut p := p
    -- The candidate for a unit.
    let mut unit? : Option ILit := none
    for l in C do
      match p.litValue? l with
      | some true =>
        return (p, .notUnit)
      | some false => ()
      | none =>
        if let .some u := unit? then
          if u != l then
            return (p, .notUnit)
        unit? := some l
    match unit? with
    | none => return (p, .contradiction)
    | some u => return (p.setLit u, .extended)

end UnitPropagator