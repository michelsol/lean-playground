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

-- require std from git "https://github.com/leanprover/std4" @ "main"
-- require mathlib from "../mathlib4"

require std from git "https://github.com/leanprover/std4" @ "ee49cf8fada1bf5a15592c399a925c401848227f"
require Qq from git "https://github.com/leanprover-community/quote4" @ "ccba5d35d07a448fab14c0e391c8105df6e2564c"
require aesop from git "https://github.com/leanprover-community/aesop" @ "69404390bdc1de946bf0a2e51b1a69f308e56d7a"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "31d41415d5782a196999d4fd8eeaef3cae386a5f"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "a751d21d4b68c999accb6fc5d960538af26ad5ec"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "93e820f3619d1e6ec775246653c587c04439de0c"
