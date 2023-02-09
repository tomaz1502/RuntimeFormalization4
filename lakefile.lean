import Lake
open Lake DSL

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
