import Lake
open Lake DSL

package "lean-playground" where
  -- add package configuration options here

lean_lib «LeanPlayground» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_exe "lean-playground" where
  root := `Main
