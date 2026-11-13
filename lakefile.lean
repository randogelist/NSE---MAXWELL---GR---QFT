import Lake

open Lake DSL

package nse_maxwell where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

lean_lib MaxwellEndpoint where
  srcDir := "Maxwell_Endpoint"

lean_lib NSEMaxwellForward where
  srcDir := "B <-> Maxwell/=>"

lean_lib NSEMaxwellReverse where
  srcDir := "B <-> Maxwell/<="

lean_lib SingularClosure where
  srcDir := "Fefferman_adapter/NativeSources/methlib"

lean_lib MethlibEndpoints where
  srcDir := "Fefferman_adapter"

lean_lib ClassicalMechanicsForward where
  srcDir := "B <-> ClassicalMechanics/=>"

lean_lib ClassicalMechanicsReverse where
  srcDir := "B <-> ClassicalMechanics/<="

lean_lib ClassicalMechanics where
  srcDir := "Classical_Mechanics_adapter"

lean_lib ClassicalMechanicsAssembly where
  srcDir := "ASSEMBLY"

@[default_target]
lean_lib NSEMaxwell where
  srcDir := "Fefferman_adapter"
