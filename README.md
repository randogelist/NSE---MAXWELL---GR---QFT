# Fefferman B ↔ constrained Maxwell

## Repository structure

| Directory | Scope |
|---|---|
| [Fefferman_B_adapter/](Fefferman_B_adapter/) | Exact Fefferman-B statement, shared bridge calculus, copied Mathlib/Methlib endpoints |
| [Maxwell_Endpoint/](Maxwell_Endpoint/) | Independent native Maxwell definitions, constructions, compiler configuration, and named audit |
| [B <-> Maxwell/](B%20%3C-%3E%20Maxwell/) | Equivalence derivations and the two directional proof directories |
| [Auxillary/](Auxillary/) | External runners, audit/cache targets, status, cache documentation, retained compiler evidence |
| [B <-> Maxwell/=>/](B%20%3C-%3E%20Maxwell/%3D%3E/) | Fefferman B ⇒ constrained Maxwell: actual forward proof bodies |
| [B <-> Maxwell/<=/](B%20%3C-%3E%20Maxwell/%3C%3D/) | Constrained Maxwell ⇒ Fefferman B: actual reverse proof bodies |

The four top-level content folders have the requested domain roles. `.github/` retains GitHub Actions discovery. Root files retain Lake configuration, compiler selection, repository instructions, and Git metadata. Auxiliary entry points, target lists, status, and evidence reside in `Auxillary/`.

```text
LAYOUT_PLATFORM             = LINUX / POSIX
CURRENT_SOURCE_STATUS      = A_TIER_CANDIDATE_PENDING_EXTERNAL_VALIDATION
ROOT_EXTERNAL_VALIDATION    = PENDING_CACHED_NATIVE_LINUX
ISOLATED_MAXWELL_VALIDATION  = PENDING_CACHED_NATIVE_LINUX
PRIOR_CERTIFIED_RUN         = 43348914489
REGISTERED_ROOT_TARGETS     = 226
REGISTERED_MAXWELL_TARGETS  = 52
LOCAL_LEAN_EXECUTIONS        = 0
HODGE_LEAN_INHABITANT        = NOT_SUPPLIED
HODGE_B_TIER_DERIVATION      = COMPLETE
```

Literal `<` and `>` directory names require a POSIX checkout. Active compiler: external native Linux Lean `4.34.0-rc1`. Historical Windows evidence and `Auxillary/run.cmd` remain recorded; native Windows checkout compatibility is not asserted for this literal layout.

## Exact statement

The definition occurs once, in [Classical.lean](Fefferman_B_adapter/NSEMaxwell/Classical.lean):

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
NATIVE_SOURCE_CLOSURE = Mathlib + MaxwellEndpoint.*
NATIVE_ZERO_INSTANCE = MaxwellEndpoint.zero_solution
NATIVE_ZERO_EXISTENCE = MaxwellEndpoint.zero_datum_global_instance
NATIVE_THEOREM_COUNT = 23
NATIVE_DEFINITION_TYPE_TARGET_COUNT = 29
ROOT_BUILD_AND_AUDIT = PENDING_CACHED_EXTERNAL_LINUX
ISOLATED_BUILD_AND_AUDIT = PENDING_CACHED_EXTERNAL_LINUX
```

[Native scope and certification contract](Maxwell_Endpoint/MAXWELL_ENDPOINT_A_TIER.txt). The candidate `zero_solution` theorem constructs the actual zero fields for every real `ν`, `c`, and arbitrary harmonic mean `m`. `zero_datum_global_instance` combines admissibility with that global witness. These endpoints do not prove the arbitrary-data existence proposition `MaxwellB`.

## Directional Lean endpoints

```lean
NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_periodicAnalyticLaws
NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_periodicAnalyticLaws
NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_fourierHodgeLaws
NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_fourierHodgeLaws
```

Every declaration retains its explicit analytic premise. The direction roots contain the original construction proofs. [AnalyticContracts.lean](Fefferman_B_adapter/NSEMaxwell/AnalyticContracts.lean) contains their shared objects and assumptions. [AnalyticBridge.lean](Fefferman_B_adapter/NSEMaxwell/AnalyticBridge.lean) assembles the two directions; existing namespaces and theorem statements are preserved.

The reduced root remains

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED :
  NSEMaxwell.Bridge.FourierHodgeLaws →
  NSEMaxwell.Classical.ExactEquivalence
```

The four Hodge fields have a complete mathematical derivation in [FOURIER_HODGE_COMPOSITION_B_TIER.txt](B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt). Their Lean implementation remains deferred. Reorganization does not discharge an analytic premise.

## Copied public endpoints

[Fefferman_B_adapter/Endpoints/](Fefferman_B_adapter/Endpoints/) contains 22 selected declarations, 14 byte-exact source snapshots, signatures, imports, hashes, upstream URLs, and audit boundaries.

```text
Mathlib pin = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
Methlib pin = e9cf90726b8544a268469ebc8fa6634e9c713e07
Selection   = 16 core + 4 optional + 1 auxiliary + 1 reference
```

The `.lean.txt` copies are reference sources. The active Mathlib implementation remains the pinned cached dependency. Methlib source ports and the Hodge inhabitant require the later integration specified in [INTEGRATION_PLAN.md](B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md).

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
Theorem audit     = fresh; 226 integrated targets + 52 standalone targets
Allowed axioms    = propext, Classical.choice, Quot.sound
```

The freshness check and final build include both reduced direction modules and the native Maxwell endpoint. Source manifests include the Maxwell, adapter, and two directional roots. Isolated package validation uses the Maxwell folder without other project source. No cache cleaning is performed.

[formalization-status.json](Auxillary/formalization-status.json) records scope and evidence. [Retained evidence](Auxillary/evidence/) preserves prior compiler artifacts byte-for-byte; each certificate identifies its original source commit and layout.

## Prior matching proof-source certificate

[Native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147) passed the reorganized build and all **174/174** named theorem audits. Certified proof-source commit: `be8376a08573a7789e36b68c2bc48178aa6f53c3`. All **30/30** Lean input hashes matched that certified source snapshot. All four new directional declarations and the exact reduced root have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom dependencies.

[Permanent evidence](Auxillary/evidence/linux-43345557147/) preserves all 65 artifact files. Compiler, dependency, and project cache restorations are recorded in the run. Formal status: **CONDITIONAL_FORMAL_CLOSURE**; the `FourierHodgeLaws` premise remains explicit.

## Prior Auxillary layout certificate

[Native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489) passed the relocated runner, build validation, and all **174/174 fresh** named theorem audits. Source commit: `b02425040a217a94855cfa52934e303f12fe80de`. All **30/30** Lean source hashes matched that source snapshot; compiler, dependency, and project caches were exact hits. Lake's transitive trace freshness check returned `0`, yielding **zero module rebuilds** and a fresh theorem audit.

[Retained evidence](Auxillary/evidence/linux-43348914489/) preserves all **38 original artifact files**. [Audit summary](Auxillary/evidence/linux-43348914489/audit-summary.json) records `PASS_STANDARD_ONLY`; the explicit `FourierHodgeLaws` premise remains unresolved. The certificate covers 289 source inputs, with the recorded CRLF checkout normalization for `Auxillary/run.cmd`.

The Maxwell source extraction requires the pending root and isolated-package compiler/audit certificates. Historical evidence remains scoped to its original source commit.
