import Lake
open Lake DSL

package «divseq2» {
  -- add package configuration options here
}

lean_lib «Divseq2» {
  -- add library configuration options here
}

@[default_target]
lean_exe «divseq2» {
  root := `Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
