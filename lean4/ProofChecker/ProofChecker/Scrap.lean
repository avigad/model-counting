import ProofChecker.Data.Cnf
import ProofChecker.Cat

/-! Code that is no longer needed. -/

open CheckerState

/-- Check that `C` is either implied by UP, or is a RAT on its first literal, the *pivot*.
For CRAT we also ensure that the pivot is an extension variable.
`posHints` and `negHints` are as in LRAT -/
def checkRat (C : Clause Nat) (posHints : List Nat) (negHints : List (Nat × List Nat)) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithHints notC posHints | do
    log s!"({C}) implied by UP"
    return /- contradiction found, implied by UP -/
  let some pivot := C.firstLit? | throw <| .upNoContradiction τ
  let st ← get
  if pivot.var ≤ st.originalVars then throw <| .varNotExtension pivot.var
  let negHints := negHints.foldl (init := Std.HashMap.empty) fun acc (i, hs) => acc.insert i hs
  -- TODO this would be much more efficient if we only looped over clauses containing the pivot
  st.clauseDb.forM fun i (Ci, _) => do
    if !Ci.contains pivot.negate then return
    for lit in C do
      -- resolvent is a tautology
      if lit ≠ pivot ∧ Ci.contains lit.negate then return
    let some hs := negHints.find? i | throw <| .missingHint i pivot
    let τ' := τ ++ PropAssignment.mk (Ci.filterMap fun x => if x ≠ pivot then some x.negate else none)
    if let some τ' ← propagateWithHints τ' hs then
      throw <| .upNoContradiction τ'
  log s!"({C}) RAT on {pivot}"

partial def propagateWithoutHints (τ : PropAssignment Nat) : CheckerM (Option (PropAssignment Nat)) := do
  -- awfully inefficient UP implementation
  let τ' ← (← get).clauseDb.foldM (init := some τ) fun τ _ (Ci, _) => do
    let some τ := τ | return none
    match τ.reduceClause Ci with
    | none => return some τ
    | some [] => return none
    | some [l] => return some (τ.extend l)
    | some _ => return some τ
  match τ' with
  | none => return none
  | some τ' =>
    if τ' == τ then return τ
    else propagateWithoutHints τ'

def checkAtWithoutHints (C : Clause Nat) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithoutHints notC | do
    log s!"({C}) implied by UP"
    return
  throw <| .upNoContradiction τ

def checkRatWithoutHints (C : Clause Nat) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithoutHints notC | do
    log s!"({C}) implied by UP"
    return
  let some pivot := C.firstLit? | throw <| .upNoContradiction τ
  let st ← get
  if pivot.var ≤ st.originalVars then throw <| .varNotExtension pivot.var
  st.clauseDb.forM fun _ (Ci, _) => do
    if !Ci.contains pivot.negate then return
    for lit in C do
      if lit ≠ pivot ∧ Ci.contains lit.negate then return
    let τ' := τ ++ PropAssignment.mk (Ci.filterMap fun x => if x ≠ pivot then some x.negate else none)
    if let some τ' ← propagateWithoutHints τ' then
      throw <| .upNoContradiction τ'
  log s!"({C}) RAT on {pivot}"
