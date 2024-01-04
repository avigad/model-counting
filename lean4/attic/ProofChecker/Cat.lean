/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.Array.Basic
import Lean.Data.HashSet

/-! OUTDATED FILE -/

import ProofChecker.Data.Dimacs
import ProofChecker.Data.ClauseDb

def Except.ofOption (e : ε) : Option α → Except ε α
  | none   => .error e
  | some x => .ok x

/-- A step in a CRAT proof. Clause indices have type `α`, variables type `ν` and literals type `β`. -/
inductive CratStep (α ν β : Type)
  | /-- Add asymmetric tautology. -/
    addAt (idx : α) (C : Array β) (upHints : Array α)
  | /-- Delete asymmetric tautology. -/
    delAt (idx : α) (upHints : Array α)
  | /-- Declare product operation. -/
    prod (idx : α) (x : ν) (ls : Array β)
  | /-- Declare sum operation. -/
    sum (idx : α) (x : ν) (l₁ l₂ : β) (upHints : Array α)
  | /-- Delete operation. -/
    delOp (x : ν)
  deriving Repr

-- ~~maybe~~ nah
class SignedType (α : Type u) (β : outParam $ Type v) :=
  embed : α → β
  inj : ∀ a a', embed a = embed a' → a = a'

-- instance : SignedType Nat Int := sorry
-- instance : SignedType UInt8 Int8 := sorry
-- etc

namespace CratStep

instance [ToString α] [ToString ν] [ToString β] : ToString (CratStep α ν β) where
  toString := fun
    | addAt idx C upHints => s!"{idx} a {C} (hints: {upHints})"
    | delAt idx upHints => s!"dc {idx} (hints: {upHints})"
    | prod idx x ls => s!"{idx} p {x} {ls.map toString |>.toList |> " ".intercalate}"
    | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} (hints: {upHints})"
    | delOp x => s!"do {x}"

open Dimacs in
/-- Makes a step given a DIMACS line. -/
def ofDimacs (tks : List Token) : Except String (CratStep Nat Nat Int) := do
  let toUpHints (tks : List Token) : Except String (Array Nat) := do
    if let [.str "*"] := tks then
      throw s!"got unhinted proof, but all hints need to be filled in"
    List.toArray <$> tks.mapM (·.getInt? |> Except.ofOption "expected int" |>.map Int.natAbs)
  let posInt (x : Int) : Except String Nat := do
    if x < 0 then throw s!"expected positive int {x}"
    return x.natAbs
  let clauseOfLitTks (tks : List Token) : Except String (Array Int) := do
    List.toArray <$> tks.mapM (·.getInt? |> Except.ofOption "expected int")
  match tks with
  | [.int idx, .str "a"] ++ tks =>
    let grps := List.splitOn (.int 0) tks
    let lits :: pf? := grps | throw s!"expected clause in '{grps}'"
    let pf := pf?.head?.getD []
    return .addAt (← posInt idx) (← clauseOfLitTks lits) (← toUpHints pf)
  | [.str "dc", .int idx] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .delAt (← posInt idx) (← toUpHints pf)
  | [.int idx, .str "p", .int v] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let ls ← tks.dropLast.mapM (·.getInt? |> Except.ofOption "expected int")
    if ls.length < 2 then throw s!"expected at least two literals"
    return .prod (← posInt idx) (← posInt v) ls.toArray
  | [.int idx, .str "s", .int v, .int l₁, .int l₂] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .sum (← posInt idx) (← posInt v) l₁ l₂ (← toUpHints pf)
  | [.str "do", .int v] =>
    return .delOp (← posInt v)
  | [_, .str "i"] ++ _ =>
    throw s!"input clause command is deprecated"
  | _ => throw s!"unexpected line"

def readDimacsFile (fname : String) : IO (Array <| CratStep Nat Nat Int) := do
  let mut pf := #[]
  for ln in (← Dimacs.tokenizeFile fname) do
    match CratStep.ofDimacs ln with
    | .ok s => pf := pf.push s
    | .error e => throw <| IO.userError s!"failed to parse line '{ln}': {e}"
  return pf

end CratStep

namespace CountingScheme

/-- Every node in a scheme is a variable of type `ν`, defined as equivalent to some combination
of literals. -/
inductive Node β
  /- Extension variable for sum of subdiagrams with disjoint assignments. -/
  | sum (a b : β)
  /- Extension variable for product of subdiagrams with disjoint dependency sets. -/
  | prod (ls : Array β)
  deriving Repr, Inhabited

-- G.toPropForm = φ
-- ∀ τ, τ ⊨ G (could be different implementation of ⊨ ) ↔ τ ⊨ φ
structure Graph (ν β : Type) [BEq ν] [Hashable ν] where
  /--
  `nodes x = y` when x ↔ y, i.e. the node `y` defines the extension variable `x`
  -/
  nodes : Std.HashMap ν (Node β) := {}

variable {ν β : Type} [BEq ν] [Hashable ν]

def Graph.empty : Graph ν β := {}

inductive GraphUpdateError ν where
  | varAlreadyExists (x : ν)
  | unknownVar (x : ν)

instance [ToString ν] : ToString (GraphUpdateError ν) where
  toString := fun
    | .varAlreadyExists x => s!"variable '{x}' already exists"
    | .unknownVar x => s!"unknown extension variable '{x}'"

def Graph.update (g : Graph ν β) : CratStep α ν β → Except (GraphUpdateError ν) (Graph ν β)
  | .prod _ x ls =>
    if g.nodes.contains x then
      throw <| .varAlreadyExists x
    else
      return { g with nodes := g.nodes.insert x <| .prod ls }
  | .sum _ x l₁ l₂ _ =>
    if g.nodes.contains x then
      throw <| .varAlreadyExists x
    else
      return { g with nodes := g.nodes.insert x <| .sum l₁ l₂ }
  | .delOp x =>
    if !g.nodes.contains x then
      throw <| .unknownVar x
    else
      return { g with nodes := g.nodes.erase x }
  | _ => .ok g

--  A-->|text|B
/-
def Graph.toMermaidChart [ToString ν] [ToString β] (g : Graph ν β) : String := Id.run do
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

end CountingScheme

structure CheckerState where
  inputCnf : Array (Array Int)
  verbose : Bool := false
  originalVars : Nat := inputCnf.flatten.map Int.natAbs |>.getMax? (· < ·) |>.getD 0
  /-- The clause database. -/
  clauseDb' : ClauseDb Nat Int := {}
  /-- Which clauses are counting schema definition clauses. -/
  schemaDefs : Lean.HashSet Nat := {}
  /-- The indices of all clauses a given literal occurs in. -/
  occurs : Std.HashMap Int (Array Nat) := {}
  /-- We have `x ↦ xs` when `x` is an extension variable and `xs = D(x)`, i.e. the set of all
  variables `x` transitively depends on. Invariant: an extension variable is in `depends` iff
  it has been introduced. -/
  depends : Std.HashMap Nat (Lean.RBTree Nat compare) := {}
  /-- We have `x ↦ xs` when `x` is any variable and `xs` is the set of all ext vars which *directly*
  (not transitively) depend on it. -/
  revDeps : Std.HashMap Nat (Lean.RBTree Nat compare) := {}
  /-- The index of the first clause together with the number of clauses defining an extension
  variable. -/
  extDefClauses : Std.HashMap Nat (Nat × Nat) := {}
  scheme : CountingScheme.Graph Nat Int := {}
  trace : Array String := #[]

  -- /--
  -- `backrefs x` lists all the vars which directly reference this var.
  -- We use this to implement abstraction / collapse nodes.
  -- -/
  -- backrefs : Std.HashMap ν (Std.HashSet ν)

instance : Inhabited CheckerState := ⟨{ inputCnf := #[] }⟩

inductive CheckerError where
  | graphUpdateError (err : CountingScheme.GraphUpdateError Nat)
  | duplicateClauseIdx (idx : Nat)
  | wrongClauseIdx (idx : Nat)
  | hintNotUnit (idx : Nat)
  | upNoContradiction (τ : PartPropAssignment Int)
  | varNotExtension (x : Nat)
  | varHasRevDeps (x : Nat)
  | duplicateExtVar (x : Nat)
  | unknownExtVar (x : Nat)
  | prodNotDisjoint (xs : List Nat)
  | finalStateInputNotDeleted (C : Array Int)
  | finalStateNotOneUnit (C : Array Int)

namespace CheckerError

instance : ToString CheckerError where
  toString := fun
    | graphUpdateError e => s!"graph update error: {e}"
    | duplicateClauseIdx idx => s!"duplicate clause index: {idx}"
    | wrongClauseIdx idx => s!"wrong clause index: {idx}"
    | hintNotUnit idx => s!"hinted clause at {idx} did not become unit"
    | upNoContradiction τ => s!"unit propagation did not derive contradiction (final assignment {@id (Std.HashMap Int _) τ |>.toList})"
    | varNotExtension x => s!"variable '{x}' is not an extension variable"
    | varHasRevDeps x => s!"variable '{x}' cannot be removed as others depend on it"
    | duplicateExtVar x => s!"extension variable '{x}' already introduced"
    | unknownExtVar x => s!"unknown extension variable '{x}'"
    | prodNotDisjoint xs => s!"variables {xs} have non-disjoint dependency sets"
    | finalStateInputNotDeleted C => s!"proof done but input clause {C} was not deleted"
    | finalStateNotOneUnit C => s!"proof done but leftover clause {C} found"

end CheckerError

namespace CheckerState

abbrev CheckerM := ExceptT CheckerError <| StateM CheckerState

def withTraces (f : Array String → String) (x : CheckerM Unit) : CheckerM Unit := do
  if (← get).verbose then
    let prevTrace ← modifyGet fun st => (st.trace, { st with trace := #[] })
    try x
    finally
      modify fun st => { st with trace := prevTrace.push <| f st.trace }
  else
    x

def log_ (msg : Unit → String) : CheckerM Unit := do
  modify fun st =>
    if st.verbose then { st with trace := st.trace.push <| msg () }
    else st

syntax "log! " interpolatedStr(term) : term
macro_rules
  | `(log! $interpStr) => `(log_ fun _ => s!$interpStr)

def addClause (idx : Nat) (C : Array Int) (schemaDef : Bool) : CheckerM Unit := do
  if (← get).clauseDb'.contains idx then
    throw <| .duplicateClauseIdx idx
  log! "adding clause {idx} ↦ {C}"
  modify fun st =>
    if schemaDef then
      { st with
        clauseDb' := st.clauseDb'.addClause idx C
        schemaDefs := st.schemaDefs.insert idx }
    else
      { st with clauseDb' := st.clauseDb'.addClause idx C }

def delClause (idx : Nat) : CheckerM Unit := do
  if !(← get).clauseDb'.contains idx then
    throw <| .wrongClauseIdx idx
  log! "deleting {(← get).clauseDb'.getClause idx}"
  modify fun st => { st with clauseDb' := st.clauseDb'.delClause idx }

def getClause (idx : Nat) : CheckerM (Array Int) := do
  let st ← get
  match st.clauseDb'.getClause idx with
  | none => throw <| .wrongClauseIdx idx
  | some x => return x

/-- Add an extension variable `x`. `ds` are the vars `x` depends on. If `ensureDisjoint = true`,
the dependency sets of `ds` must be pairwise disjoint. -/
def addExtVar (x : Nat) (ds : List Nat) (ensureDisjoint := false) : CheckerM Unit := do
  let st ← get
  if st.depends.contains x then
    throw <| .duplicateExtVar x

  let depsOf (x : Nat) := do
    match st.depends.find? x with
    | some ds => return ds
    | none =>
      if x > st.originalVars then
        throw <| .unknownExtVar x
      else
      -- TODO introduce these at the start and maintain invariant that `st.depends`
      -- contains all depsets of all present variables
        return Lean.RBTree.ofList [x]

  let mut allDeps ← depsOf ds.head!
  allDeps := allDeps.insert ds.head!
  for d in ds.tail! do
    let deps ← depsOf d
    -- TODO HashSet instead of RBTree?
    if ensureDisjoint ∧ deps.any (allDeps.contains ·) then
      throw <| .prodNotDisjoint ds
    allDeps := deps.fold (init := allDeps) fun acc x => acc.insert x |>.insert d

  let mut revDeps := st.revDeps
  for d in ds do
    let dRevDeps := revDeps.find? d |>.getD {} |>.insert x
    revDeps := revDeps.insert d dRevDeps

  set { st with
    depends := st.depends.insert x allDeps
    revDeps
  }

def delExtVar (x : Nat) : CheckerM Unit := do
  let st ← get
  if x ≤ st.originalVars then
    throw <| .varNotExtension x
  if !(st.revDeps.find? x |>.getD {} |>.isEmpty) then
    throw <| .varHasRevDeps x
  set { st with
    depends := st.depends.erase x
    revDeps := st.revDeps.erase x
  }

/-- Check if `C` is an asymmetric tautology wrt the clause database. -/
def checkAtWithHints (C : Array Int) (hints : Array Nat) : CheckerM Unit := do
  let st ← get
  match st.clauseDb'.unitPropWithHints (C.foldl (init := .empty) fun acc l => acc.insert (-l) ()) hints with
  | .contradiction =>
    log! "{C} implied by UP"
    return
  | .extended τ => throw <| .upNoContradiction τ
  | .wrongHint hint => throw <| .hintNotUnit hint

def updateGraph (step : CratStep Nat Nat Int) : CheckerM Unit := do
  let st ← get
  match st.scheme.update step with
  | .ok g => set { st with scheme := g }
  | .error e => throw <| .graphUpdateError e

def update (step : CratStep Nat Nat Int) : CheckerM Unit :=
  withTraces (fun ts => s!"{step}:\n\t" ++ ("\n\t".intercalate ts.toList)) do
    match step with
    | .addAt idx C pf =>
      checkAtWithHints C pf
      addClause idx C false
    | .delAt idx pf =>
      let C ← getClause idx
      -- The clause must be AT by everything except itself.
      delClause idx
      checkAtWithHints C pf
    | step@(.prod idx x ls) =>
      addExtVar x (ls.toList.map Int.natAbs) (ensureDisjoint := true)
      addClause idx (ls.map (-·) |>.push x) true
      let _ ← ls.mapIdxM fun i l =>
        addClause (idx+1+i) #[-x, l] true
      modify fun st => { st with extDefClauses := st.extDefClauses.insert x (idx, ls.size + 1) }
      updateGraph step
    | step@(.sum idx x l₁ l₂ pf) =>
      let C := #[-l₁, -l₂]
      checkAtWithHints C pf
      addExtVar x [l₁.natAbs, l₂.natAbs]
      addClause idx #[-x, l₁, l₂] true
      addClause (idx+1) #[x, -l₁] true
      addClause (idx+2) #[x, -l₂] true
      modify fun st => { st with extDefClauses := st.extDefClauses.insert x (idx, 3) }
      updateGraph step
    | .delOp x =>
      match (← get).extDefClauses.find? x with
      | none => throw <| .unknownExtVar x
      | some (idx, n) =>
        delExtVar x
        for i in [:n] do
          delClause (idx+i)
        modify fun st => { st with extDefClauses := st.extDefClauses.erase x }
        updateGraph step

def checkFinalState : CheckerM Unit := do
  let st ← get
  log! "final clauses:\n\t{st.clauseDb'}"

  -- Check that the final state of the database is just one unit clause
  -- and everything else is schema definitions. In particular, all input
  -- clauses must have been deleted.
  let _ ← st.clauseDb'.clauses.foldM (init := false) fun foundUnit i (cls, deleted) => do
    if deleted then
      return foundUnit
    if i < st.inputCnf.size then
      throw <| .finalStateInputNotDeleted cls
    if cls.size == 1 then
      if !foundUnit then
        return true
      else
        throw <| .finalStateNotOneUnit cls
    else
      let schemaDef := st.schemaDefs.contains i
      if !schemaDef then
        throw <| .finalStateNotOneUnit cls
    return foundUnit

def checkAux (pf : List (CratStep Nat Nat Int)) : ExceptT String (StateM CheckerState) Unit := do
  -- Insert all input clauses into the db.
  let _ ← (← get).inputCnf.mapIdxM fun i cl =>
    ExceptT.adapt toString <| addClause (i + 1) cl false
  for step in pf do
    ExceptT.adapt (fun e => s!"error on line '{step}': {e}") <|
      update step
  ExceptT.adapt toString <| checkFinalState

def check (cnf : Array (Array Int)) (pf : List (CratStep Nat Nat Int)) (verbose := false) : IO Unit := do
  let mut st : CheckerState := { inputCnf := cnf, verbose }
  let (ret, st') := checkAux pf |>.run st |>.run
  if verbose then
    for t in st'.trace do
      IO.println t
  if let .error e := ret then
    throw <| IO.userError s!"{e}\n\tclauses: {st'.clauseDb'}"

end CheckerState
