import Lake

open Lake DSL

package nse_gr where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

@[default_target]
lean_lib GRAdapter

lean_lib NSEGRForward

lean_lib NSEGRReverse
