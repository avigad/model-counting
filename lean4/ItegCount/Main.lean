import ItegCount.Parse
import Std
import Mathlib
open Std

def defaultFile := "/home/avigad/projects/model-counting/benchmarks-iteg/parity-cudd/parity-008.iteg"

def main (args : List String) : IO Unit := do
  let p ← timeit "Time spent parsing:" (readIteg $ args.getD 0 defaultFile)
  match p with
    | (numInputs, output, numIteElts, I) => do
      IO.println s!"{numInputs} {output} {numIteElts}"
      let O ← timeit "Time spent counting:" (pure (Iteg.countModels ⟨I, sorry⟩ numInputs).val)
      IO.println s!"Number of variables: {numInputs}"
      IO.println s!"Number of ite elements: {numIteElts}"
      IO.println s!"Result: {O[output]!}"
      return ()
