import ModelCount.Parse

def defaultFile := "/home/avigad/projects/model-counting/benchmarks/parity/parity-008.iteg"

def main (args : List String) : IO Unit := do
  let p ← timeit "Time spent parsing:" (readIteg $ args.getD 0 defaultFile)
  match p with
    | (numInputs, output, numIteElts, I) => do 
      let O ← timeit "Time spent counting:" (Iteg.countModels I numInputs)
      IO.println s!"Result: {O[output]}"
      IO.println s!"Number of ite elements: {numIteElts}"
      return ()
