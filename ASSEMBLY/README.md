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
remaining premises of this original root are the supplied `MaterialPathOn` and flow ODE.
The separate native `ClassicalMechanicsAssembly.L1_native` construction now discharges those
requirements for the exact smooth periodic divergence-free finite-slab scope.
The resulting root proves equation equivalence for a supplied velocity and pressure.

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

## Native flow realization and compatibility contracts

`ClassicalMechanicsAssembly.L1_native` and
`ClassicalMechanicsAssembly.CLASSICAL_MECHANICS_MATERIAL_NATIVE` have matching
external standard-only audits for their exact finite-slab statements.
The [native status record](../Auxillary/assembly/L1_FLOW_REALIZATION_A_TIER.txt)
contains the source identity and evidence.

`Literature.L1` now has a theorem body invoking the native construction.
All five historical compatibility declarations require zero custom axioms.
Their updated source is **A_TIER**: [cached Linux run 43401581626](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43401581626)
passed all 43 standard assembly, 169 native flow, and five compatibility audits.
All five original elaborated types and both legacy root proof bodies are preserved.
The scoped native material-equation root has **UNCONDITIONAL_CLOSURE**.
Selected Mathlib and Methlib call sites are indexed in
[L1_NATIVE_MATHLIB_ENDPOINTS.txt](../Auxillary/assembly/L1_NATIVE_MATHLIB_ENDPOINTS.txt).

The native statement supplies a smooth material path and inverse for each
given smooth periodic divergence-free velocity on [0,T], T>0, and proves the
exact pulled-back equation equivalence. Both endpoints and arbitrary velocity
mean are retained. Arbitrary-data NSE existence, global regularity, full
moving-region balance, and full solution-set bijection remain outside this scope.

Historical literature certificates and research/derivation records remain
preserved with their original source-specific status explicitly marked historical.

## Global NSE-B and material classical mechanics

`ClassicalMechanicsAssembly.NSEB_IFF_CM` proves
`forall nu : R, FeffermanB nu iff CMB nu`;
`NSEB_IFF_CM_POSITIVE` retains the positive-viscosity specialization.
The pointwise theorem identifies `NSSolution nu a u p` and
`CMSolution nu a u p` for the same global velocity and pressure.

`CMB` retains global smooth periodic incompressible kinematics and the initial
datum, with a single pair `(u,p)` chosen before every finite-slab flow witness.
Momentum balance is imposed by the literal material-coordinate equation.
Native L1 supplies each flow; native Piola transport supplies both directions;
ODE uniqueness proves overlap coherence. Material field regularity, initial
velocity, and exact decoding are derived. Pressure gauge and velocity mean
remain arbitrary. No global NSE existence assertion, full moving-region
integral law, or Lagrange-d'Alembert theorem follows from this equivalence.

Status: **A_TIER / UNCONDITIONAL_CLOSURE of the exact equivalence**.
[Cached Linux run 43447885685](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43447885685)
passed **247/247** named audits: 43 assembly, 199 native, and 5 compatibility.
The new four modules contribute 30 audited declarations; the exact root
imports 54 source-matched native modules. Approved axioms only:
`propext`, `Classical.choice`, `Quot.sound`.

[Exact source](ClassicalMechanicsAssembly/FlowNSEBCM.lean) ·
[Certificate](../Auxillary/assembly/NSEB_IFF_CM_A_TIER.txt) ·
[Retained evidence](../Auxillary/evidence/nseb-cm-linux-43447885685/).
