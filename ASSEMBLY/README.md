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
NEW_ASSEMBLY_STATUS = A_TIER
EXACT_ROOT_STATUS = CONDITIONAL_FORMAL_CLOSURE
FRESH_THEOREM_AXIOM_AUDITS = 43 / 43 PASS_STANDARD_ONLY
AUDITED_SOURCE = d04698bae290672d5c0b0238ff4fa0d6c2ca9b6a
```

The exports retain the canonical declarations and proof terms. Their source
files remain in `Classical_Mechanics_adapter` and `Fefferman_adapter`.
The `rfl` examples check reference/type compatibility; source identity follows
from the `export` mechanism and the recorded canonical source hashes.

The audited new root derives diffusion from the supplied smooth unit-Jacobian
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

External certification: [run 43376636262](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43376636262).
Retained [source-match certificate](../Auxillary/evidence/assembly-linux-43376636262/source-match-certificate.json),
[exact signatures and axiom log](../Auxillary/evidence/assembly-linux-43376636262/audit.log).
The audited proof source is unchanged by the documentation/evidence retention commit.

## Remaining literature input

`ClassicalMechanicsAssembly.Literature.L1` is the finite-slab flow-realization
axiom. `Literature.L2` and `Literature.L2_native` are native diffusion theorems.
Both equation closure routes now depend only on L1. The historical
`CLASSICAL_MECHANICS_MATERIAL_FROM_L1_L2` name is retained for compatibility.
The standard-only aggregate import remains unchanged.

Updated-module status: **A_TIER_CANDIDATE** pending matching external audit.
Exact contracts: [ASSEMBLY_LITERATURE_A_TIER.txt](../Auxillary/ASSEMBLY_LITERATURE_A_TIER.txt).
L1 still requires a native flow construction; the target closure remains
`CONDITIONAL_FORMAL_CLOSURE`.
