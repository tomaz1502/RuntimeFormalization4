import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package runtime {
  -- add package configuration options here
}

lean_lib Runtime {
  -- add library configuration options here
}

@[default_target]
lean_exe runtime {
  root := `Main
}
