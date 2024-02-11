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

require std from git "https://github.com/leanprover/std4" @ "6132dd32b49f17b1d300aba3fb15966e8f489432"
require Qq from git "https://github.com/leanprover-community/quote4" @ "190ec9abbc4cd43b1b6a1401722c0b54418a98b0"
require aesop from git "https://github.com/leanprover-community/aesop" @ "204c8f47bd79fba6b53d72536826a97fd58c016a"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "f5b2b6ff817890d85ffd8ed47637e36fcac544a6"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "a751d21d4b68c999accb6fc5d960538af26ad5ec"
require importGraph from git "https://github.com/leanprover-community/import-graph.git" @ "d95fb9ca08220089beb3ab486d0879edaad3f497"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "a7e85ccbdb48aea0a3377b90bc9d69cbb870f044"
