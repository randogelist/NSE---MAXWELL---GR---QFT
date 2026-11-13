import Lake

open Lake DSL

package fefferman_adapter where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

lean_lib MaxwellEndpoint where
  srcDir := "LocalDependencies/Maxwell"

lean_lib NSEMaxwellForward where
  srcDir := "LocalDependencies/Forward"

lean_lib NSEMaxwellReverse where
  srcDir := "LocalDependencies/Reverse"

lean_lib SingularClosure where
  srcDir := "NativeSources/methlib"

lean_lib MethlibEndpoints

@[default_target]
lean_lib NSEMaxwell
