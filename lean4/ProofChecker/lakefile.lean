import Lake
open Lake DSL

package ProofChecker

lean_lib ProofChecker

require mathlib from git"https://github.com/leanprover-community/mathlib4"@"master"
require Cli from git"https://github.com/mhuisi/lean4-cli"@"nightly"

@[default_target]
lean_exe checker {
  root := `Main
  -- moreLeancArgs := #["-UNDEBUG", "-Og", "-ggdb", "-g3", "-fno-omit-frame-pointer"]
  -- moreLinkArgs := #[
  --   "-fuse-ld=/usr/bin/ld",
  --   "-L/home/nawrocki/.elan/toolchains/leanprover--lean4---nightly-2022-10-31/lib"
  -- ]
}
