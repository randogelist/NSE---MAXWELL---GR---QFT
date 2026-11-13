# Fefferman B ↔ constrained Maxwell ↔ material classical mechanics

## Native NSE / marked Gaussian vacuum-sector closure

```text
ROOT_STATUS = !!!! UNCONDITIONAL_CLOSURE
ROOT = NSEGR.NativeLiterature.NSE_GR_NATIVE_LITERATURE_CLOSURE
TYPE = forall nu rho t0 : Real, 0 < nu -> rho != 0 ->
       Nonempty (NSEGR.NSEgerm nu t0 ≃ NSEGR.GRgerm nu rho t0)
SCOPE = local jointly analytic periodic NSE / normalized marked five-dimensional Gaussian vacuum sector
GLOBAL_FEFFERMAN_B_IFF_GR = OPEN
SOURCE = d5231111cbdbe8a9c686b52ae4224554d4fba48a
EXTERNAL_RUN = 43509144981
EXACT_AUDITS = 1549 / 1549 PASS_STANDARD_ONLY
SOURCE_HASHES = 373 / 373 PASS
UNRESOLVED_ANALYTIC_INPUTS = empty
FOUNDATIONAL_AXIOMS = {propext, Classical.choice, Quot.sound}
LOCAL_LEAN_EXECUTIONS = 0
```

[Ordered GR implication directory](B%20%3C-%3E%20GR/) ·
[Exact theorem](ASSEMBLY/GRAssembly/NSE_GR_NATIVE_LITERATURE_CLOSURE.lean) ·
[A-tier report](Auxillary/GR/Closure/Native/NSE_GR_NATIVE_LITERATURE_CLOSURE_A_TIER.txt) ·
[Certificate](Auxillary/GR/Closure/Native/EXTERNAL_CERTIFICATE.json) ·
[Scoped GR adapter](GR_adapter/README.md) ·
[External PASS](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43509144981)

## Classical mechanics branch

`Classical_Mechanics_adapter/` contains the actual Newtonian Cauchy stress
adapter. `B <-> ClassicalMechanics/=>` and `B <-> ClassicalMechanics/<=`
contain its two directional proofs. The first root combines the global
arbitrary-pressure-gauge equivalence and a separate finite normalized-pressure
equivalence. Both Maxwell compositions retain `FourierHodgeLaws` explicitly.

```text
CLASSICAL_MECHANICS_STATUS = A_TIER (local Cauchy root: UNCONDITIONAL_CLOSURE)
CLASSICAL_MECHANICS_THEOREM_AUDITS = 62 / PASS_STANDARD_ONLY
FULL_MOVING_REGION_AND_LDA_REFERENCE_ROOT = PENDING
LOCAL_LEAN_EXECUTIONS = 0
```

[Native adapter](Classical_Mechanics_adapter/) ·
[Directional structure](B%20%3C-%3E%20ClassicalMechanics/) ·
[Exact status](Auxillary/CLASSICAL_MECHANICS_ADAPTER_A_TIER.txt) ·
[Complete B-tier chain](Auxillary/derivations/NSE_CLASSICAL_MECHANICS_EQUIVALENCE_B_TIER.txt)

## Material equation extension

The native Piola identity, closed-slab acceleration chain rule, pressure-gradient pullback, and material equation transport have matching external Lean 4.34.0-rc1 evidence: [run 43370108226](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43370108226), 62/62 named theorem audits, approved foundational axioms only.

`ClassicalMechanics.CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION` retains a supplied smooth volume-preserving flow, literal pressure pullback, and transformed diffusion identity. Acceleration and pressure-gradient identities are derived. This is conditional equation equivalence; the full moving-region/Lagrange-d'Alembert reference root remains open. The certified material solution-proposition root below constructs its own flow on every finite slab.

[Exact material scope](Auxillary/CLASSICAL_MECHANICS_MATERIAL_A_TIER.txt) · [Material proof](Classical_Mechanics_adapter/ClassicalMechanics/MaterialBridge.lean)

## Material solution equivalence

```text
CANONICAL_CM_ROOT = ClassicalMechanicsAssembly.NSEB_IFF_CM
CANONICAL_CM_ROOT_TYPE = forall nu : Real, FeffermanB nu <-> CMB nu
CM_ROOT_STATUS = UNCONDITIONAL_CLOSURE
CM_THEOREM_AUDITS = 247 / PASS_STANDARD_ONLY
```

`CMB` quantifies one global smooth periodic incompressible velocity and pressure,
then an actual normalized volume-preserving material flow on each finite slab,
with literal pressure pullback and the material momentum equation. The root
proves equivalence of the two existence propositions; it does not prove either
existence proposition for arbitrary data.

[Root proof](ASSEMBLY/ClassicalMechanicsAssembly/FlowNSEBCM.lean) ·
[Exact certificate](Auxillary/assembly/NSEB_IFF_CM_A_TIER.txt) ·
[Cached Linux verification](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43447885685) ·
[Native source package](Auxillary/releases/NSEB_IFF_CM_3fca9683.zip)

## Canonical Gaussian quantum equivalence

```text
QUANTUM_STATUS = A_TIER (679 obligation declarations; 581 theorems)
QUANTUM_ROOT_STATUS = UNCONDITIONAL_CLOSURE_OF_CANONICAL_GAUSSIAN_EQUIVALENCE
QUANTUM_ROOT = QuantumAdapter.Obligations.NSE_B_IFF_CANONICAL_QUANTUM
QUANTUM_PROOF_COMMIT = 3c2a8f5435b4e95e779222b37637f12a57d1eea9
QUANTUM_EVIDENCE_PUBLICATION = c23237c8d229820bd2e9aa0a26191ae81b47b20b
QUANTUM_OBLIGATIONS = P1--P7 / DISCHARGED
QUANTUM_H3_TAME_CONSTANT = 512
MERGED_SOURCE_COMPILER_VALIDATION = REQUIRED_PER_PULL_REQUEST_CHECKS
LOCAL_LEAN_EXECUTIONS = 0
```

[Quantum_adapter](Quantum_adapter/) contains the concrete full-mean phase,
Born/L2/transport definitions, and canonical flow. [B <-> Quantum](B%20%3C-%3E%20Quantum/)
contains the ordered forward and reverse proofs. The exact root states
`∀ (ν : ℝ) (hν : 0 < ν), FeffermanB ν ↔ QREG (closedPhaseFlow hν)`. Its seven analytic
obligations are constructed; the root supplies no proof of either arbitrary-data
existence proposition separately. The certified H3 constant is 512; a stronger
constant of 16 is not part of this certificate.

[Exact obligation report](Auxillary/quantum/obligations/NSE_QUANTUM_P1_P7_A_TIER.txt) ·
[Root source](Quantum_adapter/QuantumAdapter/Obligations/Closure.lean) ·
[Retained evidence](Auxillary/quantum/obligations/evidence/3c2a8f5435b4e95e779222b37637f12a57d1eea9/) ·
[Certified-source CI: PASS](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43469332973) ·
[Windows replay package](Auxillary/quantum/obligations/exports/NSE_QUANTUM_P1_P7_WINDOWS_REPLAY.zip).

This quantum certificate binds the immutable proof commit above. The Maxwell
and classical mechanics certificates below retain their own recorded source
commits. External compilation and fresh theorem audits of the combined merge
candidate remain pending. The Windows replay launcher is source-prepared;
the recorded matching compiler evidence is native Linux.

## Repository structure

| Directory | Scope |
|---|---|
| [ASSEMBLY/](ASSEMBLY/) | The 25 selected native declarations, tensor Piola assembly, and supplied-flow equation transport; [exact status](Auxillary/ASSEMBLY_A_TIER.txt) |
| [Fefferman_adapter/](Fefferman_adapter/) | Independent Fefferman package, exact statement, bridge proofs, complete pinned dependency sources, native Methlib endpoints |
| [Maxwell_Endpoint/](Maxwell_Endpoint/) | Independent Maxwell package, native constructions, complete pinned dependency sources, native Methlib endpoints |
| [B <-> Maxwell/](B%20%3C-%3E%20Maxwell/) | Equivalence derivations and the two directional proof directories |
| [Auxillary/](Auxillary/) | External runners, audit/cache targets, status, cache documentation, retained compiler evidence |
| [B <-> Maxwell/=>/](B%20%3C-%3E%20Maxwell/%3D%3E/) | Fefferman B ⇒ constrained Maxwell: actual forward proof bodies |
| [B <-> Maxwell/<=/](B%20%3C-%3E%20Maxwell/%3C%3D/) | Constrained Maxwell ⇒ Fefferman B: actual reverse proof bodies |

The top-level content folders have the requested domain roles. `.github/` retains GitHub Actions discovery. Root files retain Lake configuration, compiler selection, repository instructions, and Git metadata. Auxiliary entry points, target lists, status, and evidence reside in `Auxillary/`.

```text
CANONICAL_ROOT = NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL
CANONICAL_ROOT_TYPE = NSEMaxwell.Classical.ExactEquivalence
CURRENT_FORMAL_STATUS = UNCONDITIONAL_CLOSURE
HODGE_LEAN_INHABITANT = NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant
UNRESOLVED_ROOT_ANALYTIC_PREMISES = NONE
EXTERNAL_RUN = 43373061238
CERTIFIED_SOURCE = c4c7bcdca6e652905107bb1a3102ed50d94c2e6b
FRESH_AUDITS = 400 integrated / 400 isolated Fefferman / 62 isolated Maxwell
LOCAL_LEAN_EXECUTIONS = 0
ARBITRARY_DATA_GLOBAL_EXISTENCE = OPEN
```

The canonical theorem proves the exact equivalence of the two arbitrary-data existence propositions. Its four Fourier–Hodge obligations are discharged by the concrete Lean inhabitant. The equivalence does not supply a proof of either existence proposition separately.

## Exact statement and scope

The canonical root in [FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean](Fefferman_adapter/NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean) has no analytic-law argument:

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL :
  NSEMaxwell.Classical.ExactEquivalence

-- ExactEquivalence =
--   ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
--     (FeffermanB ν ↔ MaxwellB ν c)
```

The [frozen definitions](Fefferman_adapter/NSEMaxwell/Classical.lean) preserve unforced periodic three-dimensional equations, arbitrary velocity mean, periodic pressure, and joint `ContDiffOn ℝ ∞` on the closed forward spacetime, including `t = 0`. Negative-time values are unrestricted. The original cosine-integral operators and constitutive fields are unchanged:

```text
u = m + K B
E = G[B] = B × u + ν curl B
ρ = div G[B]
J = c² curl B − DG[B](−curl G[B])
```

`FeffermanB ν` quantifies over every admissible periodic datum and asserts an actual global `NSSolution`. `MaxwellB ν c` is the corresponding constrained Maxwell existence statement. Arbitrary-data existence for either remains open.

## Fourier–Hodge construction

| Obligation | Actual Lean endpoint in `NSEMaxwell.HodgeProof` | Source |
|---|---|---|
| H1: reconstruct velocity with its actual mean | `h1_reconstruct_velocity` | [SpatialInhabitant.lean](Fefferman_adapter/FourierHodgeLaws/SpatialInhabitant.lean) |
| H2: reconstruct magnetic curl | `h2_reconstruct_curl` | [SpatialInhabitant.lean](Fefferman_adapter/FourierHodgeLaws/SpatialInhabitant.lean) |
| H3: canonical velocity and pressure smoothness through zero | `h3_canonical_smoothness` | [CanonicalInhabitant.lean](Fefferman_adapter/FourierHodgeLaws/CanonicalInhabitant.lean) |
| H4: electric Hodge identity | `h4_electric_hodge` | [SpatialInhabitant.lean](Fefferman_adapter/FourierHodgeLaws/SpatialInhabitant.lean) |
| Four-field inhabitant and exact equivalence | `fourierHodgeLaws_inhabitant`, `exact_equivalence_native` | [Inhabitant.lean](Fefferman_adapter/FourierHodgeLaws/Inhabitant.lean) |

The 19 integrated Hodge source files are byte-identical to the original Methlib source at `f927f1e31196f0be71b2581dc85f6e3fd19e0746`. They contribute 163 named theorem audits. The repository adds one canonical wrapper audit; `236 + 163 + 1 = 400` in both the integrated and isolated Fefferman inventories. The isolated Maxwell inventory remains 62.

[INTEGRATION_PLAN.md](B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md) records the implemented dependency chain. [FOURIER_HODGE_COMPOSITION_B_TIER.txt](B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt) retains the mathematical derivation unchanged.

The original conditional APIs remain available with their original signatures:

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED :
  NSEMaxwell.Bridge.FourierHodgeLaws →
  NSEMaxwell.Classical.ExactEquivalence
```

The canonical unconditional wrapper supplies the proved inhabitant. Conditional helper theorems are retained as reusable implications; their hypotheses are discharged in the root construction.

## Repository and standalone packages

| Path | Scope |
|---|---|
| [Fefferman_adapter/](Fefferman_adapter/) | Exact statement, canonical root, Hodge proof modules, complete pinned native source closure, independent 400-target package |
| [Maxwell_Endpoint/](Maxwell_Endpoint/) | Independent constrained Maxwell definitions and constructions, complete pinned native source closure, 62-target package |
| [B <-> Maxwell/](B%20%3C-%3E%20Maxwell/) | Mathematical derivations and the two directional proof roots |
| [B <-> Maxwell/=>/](B%20%3C-%3E%20Maxwell/%3D%3E/) | Fefferman B ⇒ constrained Maxwell construction |
| [B <-> Maxwell/<=/](B%20%3C-%3E%20Maxwell/%3C%3D/) | Constrained Maxwell ⇒ Fefferman B construction |
| [Auxillary/](Auxillary/) | External runners, audit inventories, status, cache records, and compiler evidence |

Both standalone packages contain the nine complete pinned dependency snapshots, including Mathlib, and the selected 39-module `SingularClosure` source closure. These 39 older Methlib modules are distinct from the 19 newly integrated Hodge files. Original declarations retain their namespaces. The source's adjusted mean-zero propositions are not substituted for the frozen arbitrary-mean target.

The Fefferman package contains byte-checked Maxwell and directional copies under `LocalDependencies/`; extraction requires no parent-directory sources. [PACKAGE.md](Fefferman_adapter/PACKAGE.md) records the package-local module roots and source-verification contract. The independent Maxwell `zero_solution` and `zero_datum_global_instance` endpoints preserve arbitrary harmonic mean; they are zero-datum witnesses, not arbitrary-data existence theorems.

Literal `<` and `>` directory names require a POSIX checkout. The active compiler is external native Linux Lean `4.34.0-rc1`. Historical Windows evidence and `run.cmd` entry points remain recorded; native Windows compatibility is not asserted for the literal repository layout.

## Current external certificate

[Native Linux run 43373061238](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43373061238), source `c4c7bcdca6e652905107bb1a3102ed50d94c2e6b`:

| Scope | Fresh named audits | Result |
|---|---:|---|
| Integrated repository | 400/400 | `PASS_STANDARD_ONLY` |
| Isolated Fefferman package | 400/400 | `PASS_STANDARD_ONLY` |
| Isolated Maxwell package | 62/62 | `PASS_STANDARD_ONLY` |

The canonical root, H1–H4, and the concrete inhabitant are included in the fresh theorem-level audits. Allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Source-manifest matching, package isolation, pinned dependency verification, native compilation, and fresh named audits jointly establish this certificate. [Matching evidence](Auxillary/evidence/linux-43373061238) records the exact source and compiler inputs.

External entry points:

```bash
bash Auxillary/run.sh
bash Fefferman_adapter/run.sh
bash Maxwell_Endpoint/run.sh
```

Compiler, dependency, compressed Mathlib, and project caches are retained. Ordinary Lake transitive traces validate reused objects; fresh theorem audits are mandatory. An object-cache hit is not a theorem certificate. [formalization-status.json](Auxillary/formalization-status.json) records the exact current scope and evidence.

## Historical certificates

All certificate statements below refer only to their recorded runs and source commits. Their original evidence files are preserved unchanged; historical unresolved-premise statements do not describe the current canonical root.

## Historical contained-source certificate: run 43359539373

[Native Linux run 43359539373](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43359539373), source `1de664f2ef5ddc11caef25ac2274278b4171ab6b`:

| Scope | Fresh named audits | Matching source files | Matching Lean inputs |
|---|---:|---:|---:|
| Integrated repository | 236/236 | 20,353/20,353 | 19,160/19,160 |
| Isolated Fefferman | 236/236 | 9,968/9,968 | 9,592/9,592 |
| Isolated Maxwell | 62/62 | 9,914/9,914 | 9,563/9,563 |

All three builds and named axiom audits passed with only `propext`, `Classical.choice`, and `Quot.sound`. Each package contains **9,515 native Lean files** across nine complete pinned dependency snapshots, including **8,853 Mathlib Lean files**, plus the selected **39 Methlib modules**. The ten selected `SingularClosure` endpoints passed the target Lean `4.34.0-rc1` compiler and named audits. Every reachable non-compiler import is contained; missing and ambiguous modules are both zero. `Init`, `Lean`, `Std`, and `Lake` remain supplied by the pinned compiler distribution.

The integrated build restored exact compiler, dependency, and project caches and passed ordinary Lake trace validation with zero module-build invocations. Standalone source checkouts were reconstructed from contained files with zero dependency-source downloads. Their separate project caches received physical copies of matching audited root objects; subsequent native build validation and fresh audits passed. Incremental module-build invocations: **72 Fefferman**, **44 Maxwell**; these counts do not assert recompilation counts. Dependency compilation objects were shared; dependency source checkouts and standalone project object directories were separate.

Artifact `14008727271` contains **242 preserved files**; ZIP SHA256:
`e3c5b60b16610af15c6f40454698e35c81228a1b44c5bf490d41a852cf354482`.

The source manifests describe the compiled source commit. Documentation/evidence publication preserves all certified Lean sources, build configuration, runners, and audit inventories. For source `1de664f2ef5ddc11caef25ac2274278b4171ab6b`, the certified reduced implication had **CONDITIONAL_FORMAL_CLOSURE**: `FourierHodgeLaws` was an explicit unresolved premise. That historical certificate did not prove arbitrary-data `FeffermanB` or `MaxwellB` existence.

[Integrated audit](Auxillary/evidence/linux-43359539373/audit-summary.json) · [Fefferman audit](Auxillary/evidence/linux-43359539373/fefferman-standalone/audit-summary.json) · [Maxwell audit](Auxillary/evidence/linux-43359539373/standalone/audit-summary.json) · [Retained evidence](Auxillary/evidence/linux-43359539373/)

## Prior matching proof-source certificate

[Native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147) passed the reorganized build and all **174/174** named theorem audits. Certified proof-source commit: `be8376a08573a7789e36b68c2bc48178aa6f53c3`. All **30/30** Lean input hashes matched that certified source snapshot. All four new directional declarations and the exact reduced root have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom dependencies.

[Permanent evidence](Auxillary/evidence/linux-43345557147/) preserves all 65 artifact files. Compiler, dependency, and project cache restorations are recorded in the run. Formal status at that source: **CONDITIONAL_FORMAL_CLOSURE**, with the `FourierHodgeLaws` premise explicit.

## Prior Auxillary layout certificate

[Native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489) passed the relocated runner, build validation, and all **174/174 fresh** named theorem audits. Source commit: `b02425040a217a94855cfa52934e303f12fe80de`. All **30/30** Lean source hashes matched that source snapshot; compiler, dependency, and project caches were exact hits. Lake's transitive trace freshness check returned `0`, yielding **zero module rebuilds** and a fresh theorem audit.

[Retained evidence](Auxillary/evidence/linux-43348914489/) preserves all **38 original artifact files**. [Audit summary](Auxillary/evidence/linux-43348914489/audit-summary.json) records `PASS_STANDARD_ONLY`; the explicit `FourierHodgeLaws` premise was unresolved at that source. The certificate covers 289 source inputs, with the recorded CRLF checkout normalization for `Auxillary/run.cmd`.

## Initial native Maxwell certificate

[Native Linux run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370) passed both build scopes at source commit `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`:

| Scope | Fresh named audits | Matching Lean input hashes |
|---|---:|---:|
| Integrated repository | **226/226** | **37/37** |
| Isolated Maxwell endpoint | **52/52** | **7/7** |

All registered axiom dependencies belong to `propext`, `Classical.choice`, and `Quot.sound`. The isolated package verified 18 source files, reused only the shared dependency cache, and compiled with independent project build objects. Its first project cache was populated after four module builds. The root used 32 incremental module-build invocations; this number is not a recompilation count.

[Integrated audit](Auxillary/evidence/linux-43351199370/audit-summary.json) · [Isolated audit](Auxillary/evidence/linux-43351199370/standalone/audit-summary.json) · [109 retained original artifact files](Auxillary/evidence/linux-43351199370/)

At source `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`, the 23 native theorem endpoints were A-tier and the bridge had type `FourierHodgeLaws → ExactEquivalence`, with **CONDITIONAL_FORMAL_CLOSURE**. That certificate supplied neither the Hodge inhabitant nor arbitrary-data global Maxwell existence.

## Adapter directory rename

```text
ADAPTER_DIRECTORY = Fefferman_adapter
FORMER_DIRECTORY = Fefferman_B_adapter
PROOF_DECLARATIONS_AND_PREMISES = UNCHANGED
RENAME_VALIDATION = PASS_CACHED_EXTERNAL_LINUX
```

[Run 43353327242](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43353327242), source `8fd783b4d977fdb1a31cf4716023148ddfa26af9`: 226/226 integrated and 52/52 isolated audits passed; 37/37 integrated and 7/7 standalone Lean input hashes match. Both scopes reused trace-validated cached objects with zero module rebuilds. The 35 proof-module files remain byte-identical under the directory rename.

[Rename evidence](Auxillary/evidence/linux-43353327242/).

## Native Windows download

[CLASSICAL_MECHANICS_WINDOWS.zip](Auxillary/releases/CLASSICAL_MECHANICS_WINDOWS.zip) contains the exact native source closure, both A-tier scope records, the B-tier reference, the 62-theorem Linux certificate, and `run.cmd` for cached external Windows Lean 4.34.0-rc1 validation. All 47 mapped source files are byte-identical to the source snapshot; Windows compiler execution is not inferred from the Linux evidence.

