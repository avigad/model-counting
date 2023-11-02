/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofChecker.Data.ICnf
import ProofChecker.Checker.CheckerCore

/-! Faster CPOG parser module.
Attempt 1: hand-rolled Nat parser, inlining, and StateM. -/

@[inline] def isWhitespace (c : UInt8) : Bool :=
  -- TODO: check the constants are folded
  c == ' '.val.toUInt8 || c == '\t'.val.toUInt8 || c == '\r'.val.toUInt8 || c == '\n'.val.toUInt8

@[inline] def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

structure ParserState where
  /-- Buffer containing the CPOG data. -/
  buf : ByteArray
  /-- Index into `buf` that we are currently processing at. -/
  pos : Nat := 0
  /-- The proof which we will output. -/
  pf : Array CpogStep := #[]
  /-- The current line. -/
  line : Nat := 0

abbrev ParserM := StateT ParserState <| Except String

/-- Convert a range of positions in a `ByteArray` into a `Nat`.
Assumes that each of those bytes has `isDigit`, otherwise the result is undefined. -/
def bytesToNat (buf : ByteArray) (s e : Nat) : Nat := Id.run do
  let mut ret : Nat := 0
  for i in [s:e] do
    ret := ret * 10 + (buf[i]!.val - 48)
  return ret

/-- Read a single byte without advancing the cursor.

This never fails: if EOI is encountered, `0` is returned.
Conversely, any null bytes in the actual file are treated like EOI. -/
@[inline] def readByte : ParserM UInt8 := do
  let st ← get
  if h : st.pos < st.buf.size then
    return st.buf[st.pos]
  else
    return 0

@[inline] def advance : ParserM Unit :=
  modify fun st => { st with pos := st.pos + 1 }

@[inline] def consumeByte : ParserM UInt8 := do
  let b ← readByte
  advance
  return b

def pushProofStep (step : CpogStep) : ParserM Unit :=
  modify fun st => { st with pf := st.pf.push step }

/-- Consume `\w+`. EOI is not accepted.

Convention: call this eagerly when it makes sense
rather than have callees do it. -/
@[inline] def consumeWhitespace : ParserM Unit := do
  let b ← consumeByte
  if !isWhitespace b then
    throw s!"expected whitespace, got '{Char.ofNat b.toNat}'"
  let mut b ← readByte
  while isWhitespace b do
    advance
    b ← readByte

/-- Consume a positive natural number or a DIMACS `0`-terminator.
`0` is returned only on a terminator. -/
@[inline] def consumeNat : ParserM Nat := do
  let pStart := (← get).pos
  let b ← consumeByte
  if b == '0'.val.toUInt8 then
    return 0
  if !isDigit b then
    throw s!"expected positive natural number or 0-terminator, got '{Char.ofNat b.toNat}' at {(← get).pos}"
  let mut b ← readByte
  while isDigit b do
    advance
    b ← readByte
  let pEnd := (← get).pos
  return bytesToNat (← get).buf pStart pEnd

@[inline] def consumePNat : ParserM PNat := do
  let n ← consumeNat
  if h : 0 < n then
    return ⟨n, h⟩
  else
    throw s!"{(← get).line}: expected positive natural number, got 0 at {(← get).pos}\n
    state: {(← get).pf}"

/-- Consume a non-zero integer or a DIMACS `0`-terminator.
`0` is returned only on a terminator. -/
@[inline] def consumeInt : ParserM Int := do
  let b ← readByte
  if b == '0'.val.toUInt8 then
    advance
    return 0
  if b == '-'.val.toUInt8 then
    advance
    let n ← consumePNat
    return -n.val
  if !isDigit b then
    throw s!"expected a digit or '-', got '{Char.ofNat b.toNat}' at {(← get).pos}"
  let n ← consumePNat
  return n.val

@[inline] def consumeILit : ParserM ILit := do
  let i ← consumeInt
  if h : i ≠ 0 then
    return ⟨i, h⟩
  else
    throw "expected non-zero integer, got 0"

@[inline] def consumePNats : ParserM (Array PNat) := do
  let mut n ← consumeNat
  let mut a := #[]
  while h : 0 < n do
    a := a.push ⟨n, h⟩
    consumeWhitespace
    n ← consumeNat
  return a

-- TODO: ClauseIdx should be PNat
@[inline] unsafe def consumeNatsUnsafe : ParserM (Array Nat) := do
  let a ← consumePNats
  return unsafeCast a

@[implemented_by consumeNatsUnsafe, inline]
def consumeNats : ParserM (Array Nat) := do
  let a ← consumePNats
  return a.map (·.val)

@[inline] def consumeILits : ParserM (Array ILit) := do
  let mut i ← consumeInt
  let mut a := #[]
  while h : i ≠ 0 do
    a := a.push ⟨i, h⟩
    consumeWhitespace
    i ← consumeInt
  return a

/-- Consume arbitrary characters until either a newline or EOI is seen. -/
def consumeComment : ParserM Unit := do
  let mut b ← consumeByte
  while b != '\n'.val.toUInt8 && b != 0 do
    b ← consumeByte

/-- Consume an `a` step and add it to the proof. -/
def consumeAdd (idx : PNat) : ParserM Unit := do
  let C ← consumeILits
  consumeWhitespace
  let hints ← consumeNats
  pushProofStep (.addAt idx.val C hints)

/-- Consume a `d` step and add it to the proof. -/
def consumeDel : ParserM Unit := do
  let idx ← consumePNat
  consumeWhitespace
  let hints ← consumeNats
  pushProofStep (.delAt idx.val hints)

/-- Consume a `p` step and add it to the proof. -/
def consumeProd (idx : PNat) : ParserM Unit := do
  let x ← consumePNat
  consumeWhitespace
  let ls ← consumeILits
  pushProofStep (.prod idx.val x ls)

/-- Consume an `s` step and add it to the proof. -/
def consumeSum (idx : PNat) : ParserM Unit := do
  let x ← consumePNat
  consumeWhitespace
  let l₁ ← consumeILit
  consumeWhitespace
  let l₂ ← consumeILit
  consumeWhitespace
  let hints ← consumeNats
  pushProofStep (.sum idx x l₁ l₂ hints)

/-- Consume an `r` step and add it to the proof. -/
def consumeRoot : ParserM Unit := do
  let r ← consumeILit
  pushProofStep (.root r)

partial def consumeProof : ParserM Unit := do
  let mut b ← readByte
  while b != 0 do
    if b == 'c'.val.toUInt8 then
      consumeComment
    else if b == 'r'.val.toUInt8 then
      advance
      consumeWhitespace
      consumeRoot
    else if b == 'd'.val.toUInt8 then
      advance
      consumeWhitespace
      consumeDel
    else if isWhitespace b then
      advance
    else
      let idx ← consumePNat
      consumeWhitespace
      let cmd ← consumeByte
      consumeWhitespace
      if cmd == 'a'.val.toUInt8 then
        consumeAdd idx
      else if cmd == 'p'.val.toUInt8 then
        consumeProd idx
      else if cmd == 's'.val.toUInt8 then
        consumeSum idx
      else
        throw s!"expected a | d | p | s, got '{Char.ofNat b.toNat}'"
    b ← readByte

def CpogStep.readDimacsFileFast (fname : String) : IO (Array CpogStep) := do
  let buf ← IO.FS.readBinFile fname
  match consumeProof.run { buf } with
  | .ok (_, st) => return st.pf
  | .error e => throw <| IO.userError s!"error: {e}"