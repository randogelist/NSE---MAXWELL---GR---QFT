# Classical mechanics assembly

`ClassicalMechanicsAssembly` is the native Lean import root for the 25
declarations indexed as N01–N17 and NX01–NX08 in the flow/Piola B-tier register.

| Module | Exact role |
|---|---|
| [NativeEndpoints.lean](ClassicalMechanicsAssembly/NativeEndpoints.lean) | 25 source-preserving exports and elaborated reference/type checks |
| [PiolaTransport.lean](ClassicalMechanicsAssembly/PiolaTransport.lean) | Tensor Piola transport and the transformed diffusion theorem |
| [Equation.lean](ClassicalMechanicsAssembly/Equation.lean) | Both equation implications and their deterministic equivalence |
| [ClassicalMechanicsAssembly.lean](ClassicalMechanicsAssembly.lean) | Aggregate import root |

```text
NATIVE_INPUTS = 25 existing theorems, not 25 new obligations
SOURCE_REGISTRY = ../Auxillary/assembly-native-registry.json
EXACT_STATUS = ../Auxillary/ASSEMBLY_A_TIER.txt
COMPILER = external native Linux Lean 4.34.0-rc1
NEW_ASSEMBLY_STATUS = A_TIER_CANDIDATE
```

The exports retain the canonical declarations and proof terms. Their source
files remain in `Classical_Mechanics_adapter` and `Fefferman_adapter`.
The `rfl` examples check reference/type compatibility; source identity follows
from the `export` mechanism and the recorded canonical source hashes.

The proposed new root derives diffusion from the supplied smooth unit-Jacobian
path and its actual flow ODE. Pressure is defined by scalar pullback. The
remaining premise is the supplied `MaterialPathOn` and flow ODE; construction
of that path from a smooth periodic solenoidal Eulerian field remains open in
Lean. This root is equation equivalence, not full solution-set equivalence.

External cached validation:

```bash
bash Auxillary/run.sh -Phase Dependencies
bash Auxillary/run_assembly.sh
```

No local Lean execution is part of the authoring workflow.
