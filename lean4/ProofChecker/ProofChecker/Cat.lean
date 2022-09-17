import Lean.Data.HashMap
import Lean.Data.RBTree

import ProofChecker.Data.Cnf
import ProofChecker.Data.Dimacs


/-- A step in a CAT proof. Clause indices have type `α` and variables type `ν`.
As a trick, we could set `α := Clause ν` to have direct access to clauses without
going through an index mapping. -/
inductive CatStep (α ν : Type)
  | /-- Add asymmetric tautology. -/
    addAt (idx : α) (C : Clause ν) (upHints : List α)
  | /-- Delete asymmetric tautology. -/
    delAt (idx : α) (upHints : List α)
  | /-- Declare product operation. -/
    prod (idx : α) (x : ν) (ls : List (Lit ν))
  | /-- Declare sum operation. -/
    sum (idx : α) (x : ν) (l₁ l₂ : Lit ν) (upHints : List α)
  | /-- Delete operation. -/
    delOp (x : ν)
  deriving Repr

namespace CatStep

instance [ToString α] [ToString ν] : ToString (CatStep α ν) where
  toString := fun
    | addAt idx C upHints => s!"{idx} a ({C}) (hints: {upHints})"
    | delAt idx upHints => s!"dc {idx} (hints: {upHints})"
    | prod idx x ls => s!"{idx} p {x} {ls.map toString |> " ".intercalate}"
    | sum idx x l₁ l₂ upHints => s!"{idx} s {x} {l₁} {l₂} (hints: {upHints})"
    | delOp x => s!"do {x}"

open Dimacs in
/-- Makes a step given a DIMACS line. -/
def ofDimacs (tks : List Token) : Except String (CatStep Nat Nat) := do
  let toUpHints (tks : List Token) : Except String (List Nat) := do
    if let [.str "*"] := tks then
      throw s!"got unhinted proof, but all hints need to be filled in"
    tks.mapM (·.getInt? |> Except.ofOption "expected int" |>.map Int.natAbs)
  let posInt (x : Int) : Except String Nat := do
    if x < 0 then throw s!"expected positive int {x}"
    return x.natAbs
  match tks with
  | [.int idx, .str "a"] ++ tks =>
    let grps := List.splitOn (.int 0) tks
    let lits :: pf? := grps | throw s!"expected clause in '{grps}'"
    let pf := pf?.head?.getD []
    return .addAt (← posInt idx) (← Clause.ofDimacsLits lits) (← toUpHints pf)
  | [.str "dc", .int idx] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .delAt (← posInt idx) (← toUpHints pf)
  | [.int idx, .str "p", .int v] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let ls ← tks.dropLast.mapM (·.getInt? |> Except.ofOption "expected int" |>.map Lit.ofInt)
    if ls.length < 2 then throw s!"expected at least two literals"
    return .prod (← posInt idx) (← posInt v) ls
  | [.int idx, .str "s", .int v, .int l₁, .int l₂] ++ tks =>
    let some (.int 0) := tks.getLast? | throw s!"missing terminating 0"
    let pf := tks.dropLast
    return .sum (← posInt idx) (← posInt v) (Lit.ofInt l₁) (Lit.ofInt l₂) (← toUpHints pf)
  | [.str "do", .int v] =>
    return .delOp (← posInt v)
  | [_, .str "i"] ++ _ =>
    throw s!"input clause command is deprecated"
  | _ => throw s!"unexpected line"

def readDimacsFile (fname : String) : IO (Array <| CatStep Nat Nat) := do
  let mut pf := #[]
  for ln in (← Dimacs.tokenizeFile fname) do
    match CatStep.ofDimacs ln with
    | .ok s => pf := pf.push s
    | .error e => throw <| IO.userError s!"failed to parse line '{ln}': {e}"
  return pf

end CatStep

namespace CountingScheme

-- TODO: under what conditions is a counting scheme an SDD? ROBDD?

/-- Every node in a scheme is a variable of type `ν`, defined as equivalent
to a literal or a combination of variables. -/
inductive Node ν
  /- Extension variable for sum of subdiagrams with disjoint assignments. -/
  | sum (a b : Lit ν)
  /- Extension variable for product of subdiagrams with disjoint dependency sets. -/
  | prod (ls : List (Lit ν))
  deriving Repr, Inhabited

structure Graph (ν : Type) [BEq ν] [Hashable ν] where
  /--
  `nodes x = y` when x ↔ y, i.e. the node `y` defines the extension variable `x`
  -/
  nodes : Std.HashMap ν (Node ν)

variable {ν : Type} [BEq ν] [Hashable ν]

def Graph.empty : Graph ν := {
  nodes := Std.HashMap.empty }

inductive GraphUpdateError ν where
  | varAlreadyExists (x : ν)
  | unknownVar (x : ν)

instance [ToString ν] : ToString (GraphUpdateError ν) where
  toString := fun
    | .varAlreadyExists x => s!"variable '{x}' already exists"
    | .unknownVar x => s!"unknown extension variable '{x}'"

def Graph.update (g : Graph ν) : CatStep α ν → Except (GraphUpdateError ν) (Graph ν)
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
def Graph.toMermaidChart [ToString ν] (g : Graph ν) : String := Id.run do
  let mut ret := "flowchart TB\n"
  let mkArrowEnd (x : Lit ν) := if x.polarity then s!"{x.var}" else s!"|NOT|{x.var}"
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

end CountingScheme

structure CheckerState where
  inputCnf : CnfForm Nat
  originalVars : Nat := inputCnf.maxVar?.getD 0
  /-- The clause database. We store `(C, true)` for schema definition clauses
  and `(C, false)` for all other ones. -/
  clauseDb : Std.HashMap Nat (Clause Nat × Bool) := {}
  /-- The indices of all clauses a given literal occurs in. -/
  occurs : Std.HashMap (Lit Nat) (Array Nat) := {}
  /-- We have `x ↦ xs` when `x` is an extension variable and `xs = D(x)`, i.e. the set of all
  variables `x` transitively depends on. Invariant: an extension variable is in `depends` iff
  it has been introduced. -/
  depends : Std.HashMap Nat (Std.RBTree Nat compare) := {}
  /-- We have `x ↦ xs` when `x` is any variable and `xs` is the set of all ext vars which *directly*
  (not transitively) depend on it. -/
  revDeps : Std.HashMap Nat (Std.RBTree Nat compare) := {}
  /-- The index of the first clause together with the number of clauses defining an extension
  variable. -/
  extDefClauses : Std.HashMap Nat (Nat × Nat) := {}
  scheme : CountingScheme.Graph Nat := CountingScheme.Graph.empty
  trace : Array String := #[]

  -- /--
  -- `backrefs x` lists all the vars which directly reference this var.
  -- We use this to implement abstraction / collapse nodes.
  -- -/
  -- backrefs : Std.HashMap ν (Std.HashSet ν)

instance : Inhabited CheckerState := ⟨{ inputCnf := CnfForm.mk [] }⟩

inductive CheckerError where
  | graphUpdateError (err : CountingScheme.GraphUpdateError Nat)
  | duplicateClauseIdx (idx : Nat)
  | wrongClauseIdx (idx : Nat)
  | hintNotUnit (idx : Nat)
  | upNoContradiction (τ : PropAssignment Nat)
  | varNotExtension (x : Nat)
  | varHasRevDeps (x : Nat)
  | missingHint (idx : Nat) (pivot : Lit Nat)
  | duplicateExtVar (x : Nat)
  | unknownExtVar (x : Nat)
  | prodNotDisjoint (xs : List Nat)
  | finalStateInputNotDeleted (C : Clause Nat)
  | finalStateNotOneUnit (C : Clause Nat)

namespace CheckerError

instance : ToString CheckerError where
  toString := fun
    | graphUpdateError e => s!"graph update error: {e}"
    | duplicateClauseIdx idx => s!"duplicate clause index: {idx}"
    | wrongClauseIdx idx => s!"wrong clause index: {idx}"
    | hintNotUnit idx => s!"hinted clause at {idx} did not become unit"
    | upNoContradiction τ => s!"unit propagation did not derive contradiction (final assignment {τ})"
    | varNotExtension x => s!"variable '{x}' is not an extension variable"
    | varHasRevDeps x => s!"variable '{x}' cannot be removed as others depend on it"
    | missingHint idx pivot => s!"missing hint for clause {idx} resolved on '{pivot}'"
    | duplicateExtVar x => s!"extension variable '{x}' already introduced"
    | unknownExtVar x => s!"unknown extension variable '{x}'"
    | prodNotDisjoint xs => s!"variables {xs} have non-disjoint dependency sets"
    | finalStateInputNotDeleted C => s!"proof done but input clause {C} was not deleted"
    | finalStateNotOneUnit C => s!"proof done but leftover clause {C} found"

end CheckerError

namespace CheckerState

abbrev CheckerM := ExceptT CheckerError <| StateM CheckerState

def withTraces (f : Array String → String) (x : CheckerM Unit) : CheckerM Unit := do
  let prevTrace ← modifyGet fun st => (st.trace, { st with trace := #[] })
  try x
  finally
    modify fun st => { st with trace := prevTrace.push <| f st.trace }

def log (msg : String) : CheckerM Unit := do
  modify fun st => { st with trace := st.trace.push msg }

def addClause (idx : Nat) (C : Clause Nat) (schemaDef : Bool) : CheckerM Unit := do
  let st ← get
  if st.clauseDb.contains idx then
    throw <| .duplicateClauseIdx idx
  set { st with clauseDb := st.clauseDb.insert idx (C, schemaDef) }
  log s!"adding ({C})"

def delClause (idx : Nat) : CheckerM Unit := do
  let st ← get
  if !st.clauseDb.contains idx then
    throw <| .wrongClauseIdx idx
  set { st with clauseDb := st.clauseDb.erase idx }
  log s!"deleting ({st.clauseDb.find! idx})"

def getClause (idx : Nat) : CheckerM (Clause Nat × Bool) := do
  let st ← get
  match st.clauseDb.find? idx with
  | none => throw <| .wrongClauseIdx idx
  | some x => return x

/-- Reduce clause at `idx` under `τ`. Return `none` if it reduced to true. -/
def reduceClause (idx : Nat) (τ : PropAssignment Nat) : CheckerM (Option (Clause Nat)) := do
  let (C, _) ← getClause idx
  return τ.reduceClause C

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
        return Std.RBTree.ofList [x]

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

/-- Propagate units starting from the given assignment. The clauses in `hints` are expected to become
unit in the order provided, as seen in LRAT. Return the extended assignment, or `none` if a contradiction was found. -/
def propagateWithHints (τ : PropAssignment Nat) (hints : List Nat) : CheckerM (Option (PropAssignment Nat)) := do
  let mut τ := τ
  for hint in hints do
    let some C' ← reduceClause hint τ | throw <| .hintNotUnit hint
    if C'.isEmpty then return none
    let some l := C'.unit? | throw <| .hintNotUnit hint
    τ := τ.extend l
  return some τ

def checkAtWithHints (C : Clause Nat) (hints : List Nat) : CheckerM Unit := do
  let notC := PropAssignment.mk (C.map Lit.negate)
  let some τ ← propagateWithHints notC hints | do
    log s!"({C}) implied by UP"
    return
  throw <| .upNoContradiction τ

def updateGraph (step : CatStep Nat Nat) : CheckerM Unit := do
  let st ← get
  match st.scheme.update step with
  | .ok g => set { st with scheme := g }
  | .error e => throw <| .graphUpdateError e

def update (step : CatStep Nat Nat) : CheckerM Unit :=
  withTraces (fun ts => s!"{step}:\n\t" ++ ("\n\t".intercalate ts.toList)) do
    match step with
    | .addAt idx C pf =>
      checkAtWithHints C pf
      addClause idx C false
    | .delAt idx pf =>
      let (C, _) ← getClause idx
      -- The clause must be AT by everything except itself.
      delClause idx
      checkAtWithHints C pf
    | step@(.prod idx x ls) =>
      addExtVar x (ls.map (·.var)) (ensureDisjoint := true)
      let lx := Lit.ofInt x
      addClause idx (Clause.mk <| lx :: ls.map (-·)) true
      for (i, l) in ls.enum do
        addClause (idx+1+i) (Clause.mk [-lx, l]) true
      modify fun st => { st with extDefClauses := st.extDefClauses.insert x (idx, ls.length + 1) }
      updateGraph step
    | step@(.sum idx x l₁ l₂ pf) =>
      let C := Clause.mk [l₁.negate, l₂.negate]
      checkAtWithHints C pf
      addExtVar x [l₁.var, l₂.var]
      let lx := Lit.ofInt x
      addClause idx (Clause.mk [-lx, l₁, l₂]) true
      addClause (idx+1) (Clause.mk [lx, -l₁]) true
      addClause (idx+2) (Clause.mk [lx, -l₂]) true
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
  log s!"final clauses:\n\t{st.clauseDb.toList}"

  -- Check that the final state of the database is just one unit clause
  -- and everything else is schema definitions. In particular, all input
  -- clauses must have been deleted.
  let mut foundUnit := false
  for (i, cls, schemaDef) in st.clauseDb.toList do
    if i < st.inputCnf.length then
      throw <| .finalStateInputNotDeleted cls
    if cls.length == 1 then
      if !foundUnit then
        foundUnit := true
      else
        throw <| .finalStateNotOneUnit cls
    else if !schemaDef then
      throw <| .finalStateNotOneUnit cls
    
def checkAux (pf : List (CatStep Nat Nat)) : ExceptT String (StateM CheckerState) Unit := do
  -- Insert all input clauses into the db.
  -- TODO(WN): For clause db, an array where we never realloc but rather
  -- just mark clauses as deleted might be a better choice.
  for (i, cl) in (← get).inputCnf.enum do
    ExceptT.adapt toString <| addClause (i + 1) cl false
  for step in pf do
    ExceptT.adapt (fun e => s!"error on line '{step}': {e}") <|
      update step
  ExceptT.adapt toString <| checkFinalState

def check (cnf : CnfForm Nat) (pf : List (CatStep Nat Nat)) (traces := false) : IO Unit := do
  let mut st : CheckerState := { inputCnf := cnf }
  let (ret, st') := checkAux pf |>.run st |>.run
  if traces then
    for t in st'.trace do
      IO.println t
  if let .error e := ret then
    throw <| IO.userError s!"{e}\n\tclauses: {st'.clauseDb.toList}"

end CheckerState
