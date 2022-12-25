import Lake
open Lake DSL

package playground {
  -- add package configuration options here
}

lean_lib Playground {
  -- add library configuration options here
}

@[default_target]
lean_exe «program» { root := `Main }

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from "/home/user/mathlib4"

