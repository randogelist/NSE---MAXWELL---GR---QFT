import Lake
open Lake DSL
package nse_maxwell where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
lean_lib ClassicalMechanics
lean_lib ClassicalMechanicsForward
lean_lib ClassicalMechanicsReverse
lean_lib MaxwellEndpoint
lean_lib NSEMaxwell
lean_lib NSEMaxwellForward
lean_lib NSEMaxwellReverse
