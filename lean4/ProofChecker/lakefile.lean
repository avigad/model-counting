import Lake
open Lake DSL

package ProofChecker

lean_lib ProofChecker

require Cli from git"https://github.com/mhuisi/lean4-cli"@"nightly"
require std from git"https://github.com/leanprover/std4"@"main"

@[defaultTarget]
lean_exe checker {
  root := `Main
}