/-! For parsing DIMACS-like formats -/

namespace Dimacs

inductive Token where
  | int (i : Int) | str (s : String)
  deriving Repr, BEq

instance : Coe String Token :=
  ⟨Token.str⟩

instance : Coe Int Token :=
  ⟨Token.int⟩

instance : ToString Token where
  toString := fun | .int v | .str v => toString v

def Token.getInt? : Token → Option Int
  | .int i => some i
  | .str _ => none

def Token.getStr? : Token → Option String
  | .int _ => none
  | .str s => some s

def tokenizeFile (fname : String) : IO (List (List Token)) := do
  let mut lns := #[]
  for ln in (← IO.FS.lines fname) do
    let tks := ln.splitOn " " |>.filter (· ≠ "")
    if tks.isEmpty then continue
    if tks.head! == "c" then continue
    let mut ln := #[]
    for tk in tks do
      if let some i := tk.toInt? then
        ln := ln.push <| .int i
      else
        ln := ln.push <| .str tk
    lns := lns.push ln.toList
  return lns.toList

end Dimacs