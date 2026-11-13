import Lake

open Lake DSL

package nse_maxwell where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

lean_lib NSEMaxwellForward where
  srcDir := "B <-> Maxwell/=>"

lean_lib NSEMaxwellReverse where
  srcDir := "B <-> Maxwell/<="

@[default_target]
lean_lib NSEMaxwell where
  srcDir := "Fefferman_B_adapter"
