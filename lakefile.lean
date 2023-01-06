import Lake
open Lake DSL

package «theorem-proving-lean» {
  -- add package configuration options here
}

lean_lib «TheoremProvingLean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «theorem-proving-lean» {
  root := `Main
}
