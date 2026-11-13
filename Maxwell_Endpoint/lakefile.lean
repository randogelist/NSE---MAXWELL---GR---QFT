import Lake

open Lake DSL

package maxwell_endpoint where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

lean_lib SingularClosure where
  srcDir := "NativeSources/methlib"

lean_lib MethlibEndpoints

@[default_target]
lean_lib MaxwellEndpoint
