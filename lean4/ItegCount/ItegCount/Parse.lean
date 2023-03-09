import ItegCount.Iteg

namespace String

def readNum (s : Substring) : Nat × Substring := Id.run do
  let s₀ := s.dropWhile (fun c => ! c.isDigit)
  let s₁ := s₀.takeWhile Char.isDigit
  let s₂ : Substring := ⟨s₀.1, s₁.3, s₀.3⟩
  return (s₁.toNat?.get!, s₂)

end String

open Iteg

def parseIte (s : String) : IteElt := Id.run do
  let (_, s₀) := String.readNum s.toSubstring
  let (n₁, s₁) := String.readNum s₀
  let (n₂, s₂) := String.readNum s₁
  let (n₃, _) := String.readNum s₂
  return IteElt.ite n₁ n₂ n₃

partial def readItegHeader (h : IO.FS.Handle) : IO (Nat × Nat × Nat × Nat) := do
  let s ← h.getLine
  if "iteg".isPrefixOf s then
    let (n₀, s₀) := String.readNum s.toSubstring
    let (n₁, s₁) := String.readNum s₀
    let (n₂, s₂) := String.readNum s₁
    let (n₃, _) := String.readNum s₂
    return (n₀, n₁, n₂, n₃)
  else
    readItegHeader h

-- For now, only reads the first one
partial def readOutputDeclarations (h : IO.FS.Handle) : IO Nat := do
  let s ← h.getLine
  if "c Output".isPrefixOf s then
    let s ← h.getLine
    let (n₀, _) := String.readNum s.toSubstring
    return n₀
  else
    readOutputDeclarations h

partial def findItes (h : IO.FS.Handle) : IO Unit := do
  let s ← h.getLine
  if "c ITE".isPrefixOf s then
    return ()
  else
    findItes h

def readIteg (fname : String) : IO (Nat × Nat × Nat × Array IteElt) := do
  let h ← IO.FS.Handle.mk fname IO.FS.Mode.read true
  let (_, numInputs, _, numIteElts) ← readItegHeader h
  let output ← readOutputDeclarations h
  let mut I : Array IteElt := #[]
  I := I.push IteElt.fls
  I := I.push IteElt.tr
  for i in [2:numInputs+2] do
    I := I.push (IteElt.var i)
  findItes h
  for _ in [:numIteElts] do
    I := (dbgTraceIfShared "not shared!" I).push $ parseIte (← h.getLine)
  return (numInputs, output, numIteElts, I)



