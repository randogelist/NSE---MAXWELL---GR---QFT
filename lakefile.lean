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

@[default_target]
lean_lib NSEMaxwell where
  srcDir := "Fefferman_adapter"


lean_lib QuantumAdapter where
  srcDir := "Quantum_adapter"

lean_lib NSEQuantumForward where
  srcDir := "B <-> Quantum/=>"

lean_lib NSEQuantumReverse where
  srcDir := "B <-> Quantum/<="

lean_lib NSEQuantumBridge where
  srcDir := "Quantum_adapter"
