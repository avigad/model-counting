import Lake
open Lake DSL

package ItegCount

lean_lib ItegCount

require mathlib from git"https://github.com/leanprover-community/mathlib4"@"master"
require Cli from git"https://github.com/mhuisi/lean4-cli"@"nightly"

@[default_target]
lean_exe itegc {
  root := `Main
}
