import Lake
open Lake DSL

package "local-rings" where
  -- add package configuration options here

lean_lib «LocalRings» where
  -- add library configuration options here

@[default_target]
lean_exe "local-rings" where
  root := `Main
