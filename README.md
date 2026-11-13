# Fefferman B ↔ constrained Maxwell

## Classical mechanics branch

`Classical_Mechanics_adapter/` contains the actual Newtonian Cauchy stress
adapter. `B <-> ClassicalMechanics/=>` and `B <-> ClassicalMechanics/<=`
contain its two directional proofs. The first root combines the global
arbitrary-pressure-gauge equivalence and a separate finite normalized-pressure
equivalence. Both Maxwell compositions retain `FourierHodgeLaws` explicitly.

```text
CLASSICAL_MECHANICS_STATUS = A_TIER_CANDIDATE
CLASSICAL_MECHANICS_THEOREM_AUDITS = 25
FULL_MATERIAL_AND_LDA_REFERENCE_ROOT = PENDING
LOCAL_LEAN_EXECUTIONS = 0
```

[Native adapter](Classical_Mechanics_adapter/) ·
[Directional structure](B%20%3C-%3E%20ClassicalMechanics/) ·
[Exact status](Auxillary/CLASSICAL_MECHANICS_ADAPTER_A_TIER.txt) ·
[Complete B-tier chain](Auxillary/derivations/NSE_CLASSICAL_MECHANICS_EQUIVALENCE_B_TIER.txt)

## Repository structure

| Directory | Scope |
|---|---|
| [Fefferman_adapter/](Fefferman_adapter/) | Independent Fefferman package, exact statement, bridge proofs, complete pinned dependency sources, native Methlib endpoints |
| [Maxwell_Endpoint/](Maxwell_Endpoint/) | Independent Maxwell package, native constructions, complete pinned dependency sources, native Methlib endpoints |
| [B <-> Maxwell/](B%20%3C-%3E%20Maxwell/) | Equivalence derivations and the two directional proof directories |
| [Auxillary/](Auxillary/) | External runners, audit/cache targets, status, cache documentation, retained compiler evidence |
| [B <-> Maxwell/=>/](B%20%3C-%3E%20Maxwell/%3D%3E/) | Fefferman B ⇒ constrained Maxwell: actual forward proof bodies |
| [B <-> Maxwell/<=/](B%20%3C-%3E%20Maxwell/%3C%3D/) | Constrained Maxwell ⇒ Fefferman B: actual reverse proof bodies |

The four top-level content folders have the requested domain roles. `.github/` retains GitHub Actions discovery. Root files retain Lake configuration, compiler selection, repository instructions, and Git metadata. Auxiliary entry points, target lists, status, and evidence reside in `Auxillary/`.

```text
LAYOUT_PLATFORM              = LINUX / POSIX
CURRENT_PACKAGE_STATUS       = A_TIER_FOR_EXACT_AUDITED_DECLARATIONS
INTEGRATED_AUDIT_TARGETS      = 236
ISOLATED_FEFFERMAN_TARGETS    = 236
ISOLATED_MAXWELL_TARGETS      = 62
CURRENT_EXTERNAL_VALIDATION  = PASS_THREE_SCOPES_RUN_43359539373
LOCAL_LEAN_EXECUTIONS        = 0
HODGE_LEAN_INHABITANT         = NOT_SUPPLIED
HODGE_B_TIER_DERIVATION       = COMPLETE
```

Literal `<` and `>` directory names require a POSIX checkout. Active compiler: external native Linux Lean `4.34.0-rc1`. Historical Windows evidence and `Auxillary/run.cmd` remain recorded; native Windows checkout compatibility is not asserted for this literal layout.

## Contained native source packages

Both [Fefferman_adapter](Fefferman_adapter/) and [Maxwell_Endpoint](Maxwell_Endpoint/) contain native `.lean` sources for their complete application closure, all nine pinned dependency repositories including Mathlib, and the selected 39-module Methlib closure. Each package has its own Lake configuration, source manifest, native runners, source hydration and verification, and named axiom audit.

| Component | Fefferman package | Maxwell package |
|---|---|---|
| Native project modules | All 35, including byte-checked local Maxwell/direction copies | All six Maxwell modules |
| Upstream dependency sources | Complete nine-repository pinned snapshots | Identical complete snapshots |
| Native Methlib closure | 39 original `SingularClosure` modules; ten endpoint audits | Identical closure and ten endpoint audits |
| Exact named audit inventory | 236 | 62 |
| Dependency source acquisition | Contained snapshots; exact pinned Git identities reconstructed on a cache miss | Same |
| Compiler libraries | `Init`, `Lean`, `Std`, `Lake` from the pinned Lean distribution | Same |

External entry points:

```bash
bash Auxillary/run.sh
bash Fefferman_adapter/run.sh
bash Maxwell_Endpoint/run.sh
```

The native source inventories are `native-sources.json` in each package. Snapshot bytes are checked against upstream Git blob/tree identities and the actual compiler dependency sources. Existing verified dependency checkouts and compilation caches are preserved. Isolated package builds use contained source files and separate dependency source checkouts. Verified dependency compilation objects are reused; standalone project caches are seeded with physical copies of matching audited root objects and then validated by ordinary Lake traces and fresh audits.

Original Methlib declarations retain their `SingularClosure` names. The source's `Fefferman_B_0_adjust` and `AX6Statement` remain distinct from the exact arbitrary-mean target. Neither inclusion nor compilation supplies an inhabitant of `FourierHodgeLaws`.

## Exact statement

The canonical definition occurs in [Classical.lean](Fefferman_adapter/NSEMaxwell/Classical.lean):

```lean
NSEMaxwell.Classical.FeffermanB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a →
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p
```

The exact root is

```lean
NSEMaxwell.Classical.ExactEquivalence
-- ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
--   (FeffermanB ν ↔ MaxwellB ν c)
```

Scope: unforced periodic three-dimensional equations, arbitrary velocity mean, periodic pressure, joint `ContDiffOn ℝ ∞` through `t = 0`, and the frozen cosine-integral operators. The constrained Maxwell statement fixes

```text
u = m + K B
E = G[B] = B × u + ν curl B
ρ = div G[B]
J = c² curl B − DG[B](−curl G[B])
```

## Independent Maxwell endpoint

[Maxwell_Endpoint/](Maxwell_Endpoint/) contains the actual `MaxwellSolution` and `MaxwellB` definitions, their complete local source dependencies, and an independent pinned Lake package. The namespace `NSEMaxwell.Classical` and the frozen definition bodies are retained. The adapter imports this endpoint.

```text
NATIVE_IMPLEMENTATION_IMPORTS = Mathlib + MaxwellEndpoint.*
ADDITIONAL_AUDITED_SOURCE_CLOSURE = MethlibEndpoints + SingularClosure
NATIVE_ZERO_INSTANCE = MaxwellEndpoint.zero_solution
NATIVE_ZERO_EXISTENCE = MaxwellEndpoint.zero_datum_global_instance
NATIVE_THEOREM_COUNT = 23
NATIVE_DEFINITION_TYPE_TARGET_COUNT = 29
ROOT_BUILD_AND_AUDIT = PASS_NATIVE_LINUX_AND236_STANDARD_ONLY_AUDITS
ISOLATED_BUILD_AND_AUDIT = PASS_NATIVE_LINUX_AND62_STANDARD_ONLY_AUDITS
```

[Native scope and certification contract](Maxwell_Endpoint/MAXWELL_ENDPOINT_A_TIER.txt). The externally certified `zero_solution` theorem constructs the actual zero fields for every real `ν`, `c`, and arbitrary harmonic mean `m`. `zero_datum_global_instance` combines admissibility with that global witness. These endpoints do not prove the arbitrary-data existence proposition `MaxwellB`.

## Directional Lean endpoints

```lean
NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_periodicAnalyticLaws
NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_periodicAnalyticLaws
NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_fourierHodgeLaws
NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_fourierHodgeLaws
```

Every declaration retains its explicit analytic premise. The direction roots contain the original construction proofs. [AnalyticContracts.lean](Fefferman_adapter/NSEMaxwell/AnalyticContracts.lean) contains their shared objects and assumptions. [AnalyticBridge.lean](Fefferman_adapter/NSEMaxwell/AnalyticBridge.lean) assembles the two directions; existing namespaces and theorem statements are preserved.

The reduced root remains

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED :
  NSEMaxwell.Bridge.FourierHodgeLaws →
  NSEMaxwell.Classical.ExactEquivalence
```

The four Hodge fields have a complete mathematical derivation in [FOURIER_HODGE_COMPOSITION_B_TIER.txt](B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt). Their Lean implementation remains deferred. Reorganization does not discharge an analytic premise.

## Copied public endpoints

[Fefferman_adapter/Endpoints/](Fefferman_adapter/Endpoints/) contains 22 selected declarations, 14 byte-exact source snapshots, signatures, imports, hashes, upstream URLs, and audit boundaries.

```text
Mathlib pin = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
Methlib pin = e9cf90726b8544a268469ebc8fa6634e9c713e07
Selection   = 16 core + 4 optional + 1 auxiliary + 1 reference
```

The `.lean.txt` copies remain reference sources. Native Mathlib sources and the selected 39-module Methlib closure are contained in both packages and validated against the compiler inputs. Ten selected Methlib endpoints now pass target-compiler audits. Their semantic alignment with the frozen operators and the concrete Hodge inhabitant remain the integration obligations recorded in [INTEGRATION_PLAN.md](B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md).

## Cached external validation

```bash
bash Auxillary/run.sh
```

```text
Compiler          = Lean 4.34.0-rc1, native Linux / Ubuntu 24.04
Dependency pins   = unchanged
Compiler cache    = retained
Dependency cache  = exact verified predecessor fallback + current key
Project cache     = exact verified predecessor fallback + current key
Theorem audit     = fresh; 236 integrated + 236 isolated Fefferman + 62 isolated Maxwell
Allowed axioms    = propext, Classical.choice, Quot.sound
```

The freshness check and final build include both reduced direction modules and the native Maxwell endpoint. Source manifests include the Maxwell, adapter, and two directional roots. Each isolated package is validated using only its contained source files; the Fefferman folder includes byte-checked copies of the canonical Maxwell and directional modules. No cache cleaning is performed.

[formalization-status.json](Auxillary/formalization-status.json) records scope and evidence. [Retained evidence](Auxillary/evidence/) preserves prior compiler artifacts byte-for-byte; each certificate identifies its original source commit and layout.

## Contained native source certificate

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

The source manifests describe the compiled source commit. Documentation/evidence publication preserves all certified Lean sources, build configuration, runners, and audit inventories. The exact reduced implication remains **CONDITIONAL_FORMAL_CLOSURE**; `FourierHodgeLaws` remains an explicit unresolved premise, and arbitrary-data `FeffermanB`/`MaxwellB` existence is not proved.

[Integrated audit](Auxillary/evidence/linux-43359539373/audit-summary.json) · [Fefferman audit](Auxillary/evidence/linux-43359539373/fefferman-standalone/audit-summary.json) · [Maxwell audit](Auxillary/evidence/linux-43359539373/standalone/audit-summary.json) · [Retained evidence](Auxillary/evidence/linux-43359539373/)

## Prior matching proof-source certificate

[Native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147) passed the reorganized build and all **174/174** named theorem audits. Certified proof-source commit: `be8376a08573a7789e36b68c2bc48178aa6f53c3`. All **30/30** Lean input hashes matched that certified source snapshot. All four new directional declarations and the exact reduced root have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom dependencies.

[Permanent evidence](Auxillary/evidence/linux-43345557147/) preserves all 65 artifact files. Compiler, dependency, and project cache restorations are recorded in the run. Formal status: **CONDITIONAL_FORMAL_CLOSURE**; the `FourierHodgeLaws` premise remains explicit.

## Prior Auxillary layout certificate

[Native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489) passed the relocated runner, build validation, and all **174/174 fresh** named theorem audits. Source commit: `b02425040a217a94855cfa52934e303f12fe80de`. All **30/30** Lean source hashes matched that source snapshot; compiler, dependency, and project caches were exact hits. Lake's transitive trace freshness check returned `0`, yielding **zero module rebuilds** and a fresh theorem audit.

[Retained evidence](Auxillary/evidence/linux-43348914489/) preserves all **38 original artifact files**. [Audit summary](Auxillary/evidence/linux-43348914489/audit-summary.json) records `PASS_STANDARD_ONLY`; the explicit `FourierHodgeLaws` premise remains unresolved. The certificate covers 289 source inputs, with the recorded CRLF checkout normalization for `Auxillary/run.cmd`.

## Initial native Maxwell certificate

[Native Linux run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370) passed both build scopes at source commit `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`:

| Scope | Fresh named audits | Matching Lean input hashes |
|---|---:|---:|
| Integrated repository | **226/226** | **37/37** |
| Isolated Maxwell endpoint | **52/52** | **7/7** |

All registered axiom dependencies belong to `propext`, `Classical.choice`, and `Quot.sound`. The isolated package verified 18 source files, reused only the shared dependency cache, and compiled with independent project build objects. Its first project cache was populated after four module builds. The root used 32 incremental module-build invocations; this number is not a recompilation count.

[Integrated audit](Auxillary/evidence/linux-43351199370/audit-summary.json) · [Isolated audit](Auxillary/evidence/linux-43351199370/standalone/audit-summary.json) · [109 retained original artifact files](Auxillary/evidence/linux-43351199370/)

The 23 native theorem endpoints are A-tier. The reduced bridge remains `FourierHodgeLaws → ExactEquivalence`, with **CONDITIONAL_FORMAL_CLOSURE**. Historical evidence remains scoped to its recorded source commit; the Hodge inhabitant and arbitrary-data global Maxwell existence remain unresolved.

## Adapter directory rename

```text
ADAPTER_DIRECTORY = Fefferman_adapter
FORMER_DIRECTORY = Fefferman_B_adapter
PROOF_DECLARATIONS_AND_PREMISES = UNCHANGED
RENAME_VALIDATION = PASS_CACHED_EXTERNAL_LINUX
```

[Run 43353327242](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43353327242), source `8fd783b4d977fdb1a31cf4716023148ddfa26af9`: 226/226 integrated and 52/52 isolated audits passed; 37/37 integrated and 7/7 standalone Lean input hashes match. Both scopes reused trace-validated cached objects with zero module rebuilds. The 35 proof-module files remain byte-identical under the directory rename.

[Rename evidence](Auxillary/evidence/linux-43353327242/).
