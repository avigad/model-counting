import Lake
open Lake DSL

package ProofChecker

require Cli from git"https://github.com/hargoniX/lean4-cli"@"f8fe306d00b31cdfcf5d24e6c0d050e34bec6bb0"

@[defaultTarget]
lean_exe checker {
  root := `Main
}
