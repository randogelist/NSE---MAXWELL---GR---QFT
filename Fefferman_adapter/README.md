# Fefferman adapter

## Standalone native package

[PACKAGE.md](PACKAGE.md) specifies the independent package. All 35 project modules are contained here, including ten byte-identical copies under [LocalDependencies/](LocalDependencies/) of the canonical Maxwell and directional sources. Complete Mathlib and eight companion dependency snapshots reside in [NativeSources/](NativeSources/). The selected 39-module Methlib closure is native Lean source, compiled through [MethlibEndpoints.lean](MethlibEndpoints.lean) and included in the 236-target package audit.

```bash
bash Fefferman_adapter/run.sh
```

Package extraction requires no parent-directory source dependency. `scripts/hydrate_native_sources.py` reconstructs missing exact pinned dependency checkouts from contained sources. Existing valid dependency checkouts and object caches remain intact. `scripts/verify_native_sources.py` checks source inventory, upstream Git identities, cached source equality and import closure.

```text
CURRENT_PACKAGE_STATUS = A_TIER_FOR_EXACT_AUDITED_DECLARATIONS
EXTERNAL_VALIDATION = PASS_RUN_43359539373
REGISTERED_PACKAGE_AUDIT_TARGETS = 236
METHLIB_NATIVE_MODULES = 39
METHLIB_ENDPOINT_AUDITS = 10
```

## Exact Lean statement

Location: [NSEMaxwell/Classical.lean](NSEMaxwell/Classical.lean).

```lean
NSEMaxwell.Classical.FeffermanB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a →
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p
```

`NSSolution`, `FeffermanB`, and `ExactEquivalence` remain in this adapter. `Data`, actual derivatives, periodicity, cube means, joint smoothness, constitutive operators, and the constrained Maxwell statement are imported from [Maxwell_Endpoint/](../Maxwell_Endpoint/) in the integrated repository and the byte-identical [LocalDependencies/Maxwell/](LocalDependencies/Maxwell/) copies in the standalone package. Their original namespace and definition bodies are retained. A compiled proposition definition is distinct from a proof of that proposition.

## Contents

| Path | Content |
|---|---|
| [NSEMaxwell/Classical.lean](NSEMaxwell/Classical.lean) | Exact NSE solution, Fefferman-B statement, and equivalence proposition |
| [Maxwell_Endpoint/](../Maxwell_Endpoint/) | Imported native geometry, constitutive fields, and exact Maxwell statement |
| [NSEMaxwell/AnalyticContracts.lean](NSEMaxwell/AnalyticContracts.lean) | Shared magnetic-path objects and explicit analytic contracts |
| [NSEMaxwell/AnalyticReduction.lean](NSEMaxwell/AnalyticReduction.lean) | Four-field FourierHodgeLaws contract and reduction |
| [NSEMaxwell/AnalyticBridge.lean](NSEMaxwell/AnalyticBridge.lean) | Compatibility assembly of the two directions |
| [NSEMaxwell/](NSEMaxwell/) | Shared derivative, periodic integration, mean, vorticity, and constitutive calculus |
| [Endpoints/](Endpoints/) | Selected Mathlib/Methlib source copies and index |
| [NSEMaxwell/Audit.lean](NSEMaxwell/Audit.lean) | Exact signature and theorem-level axiom audit commands |

The module root remains `NSEMaxwell`; both repository and standalone Lake configurations map it to this physical directory.

Repository runners and retained compiler evidence reside in [Auxillary/](../Auxillary/). Package-local runners and verification scripts support isolated builds.

## Legacy copied endpoint boundary

```text
PUBLIC_SOURCE_COPIES   = PRESENT
LEGACY_TEXT_SNAPSHOTS = RETAINED
NATIVE_METHLIB_CLOSURE = NativeSources/methlib
TARGET_NATIVE_AUDIT = PASS_10_SELECTED_METHLIB_ENDPOINTS
HODGE_LEAN_INHABITANT  = NOT_SUPPLIED
```

Fourteen original source files are copied under `Endpoints/sources/`, with `.lean.txt` suffixes and unchanged bytes: six Mathlib files and eight Methlib files. Complete imports are recorded; the snapshots do not constitute a standalone dependency-closed package.

Mathematical composition: [FOURIER_HODGE_COMPOSITION_B_TIER.txt](../B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt).

Deferred Lean contracts: [INTEGRATION_PLAN.md](../B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md).

## Directional consumers

- [Fefferman B ⇒ Maxwell](../B%20%3C-%3E%20Maxwell/%3D%3E/).
- [Maxwell ⇒ Fefferman B](../B%20%3C-%3E%20Maxwell/%3C%3D/).

The directional base modules import `NSEMaxwell.AnalyticContracts`. Their separate reduced modules import `NSEMaxwell.AnalyticReduction`. The resulting module graph is acyclic.

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

[Integrated audit](../Auxillary/evidence/linux-43359539373/audit-summary.json) · [Fefferman audit](../Auxillary/evidence/linux-43359539373/fefferman-standalone/audit-summary.json) · [Retained evidence](../Auxillary/evidence/linux-43359539373/)

## Historical external certificates

[Native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147): build PASS; 174/174 named audits PASS_STANDARD_ONLY; 30/30 Lean input hashes matched that source snapshot. [Audit summary](../Auxillary/evidence/linux-43345557147/audit-summary.json). The conditional directions are A-tier; the Hodge inhabitant remains deferred. The relocated auxiliary runner paths also passed [native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489), source `b02425040a217a94855cfa52934e303f12fe80de`: 174/174 fresh audits, 30/30 matching Lean inputs, and zero module rebuilds after Lake trace validation. [Retained audit summary](../Auxillary/evidence/linux-43348914489/audit-summary.json).

## Initial native extraction certificate

```text
SOURCE_STATUS = A_TIER_FOR_EXACT_CONDITIONAL_BRIDGE
REGISTERED_ROOT_AUDIT_TARGETS = 226
REGISTERED_MAXWELL_AUDIT_TARGETS = 52
ROOT_EXTERNAL_VALIDATION = PASS_BUILD_AND226_FRESH_AUDITS
ISOLATED_MAXWELL_VALIDATION = PASS_BUILD_AND52_FRESH_AUDITS
HODGE_LEAN_INHABITANT = NOT_SUPPLIED
```

The native Maxwell package is upstream of this adapter in the import graph. The adapter and both implication directions retain their exact explicit hypotheses. Source extraction passed both external build and theorem-audit scopes in [run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370), source `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`.

Native witness endpoints: `MaxwellEndpoint.zero_solution` and `MaxwellEndpoint.zero_datum_global_instance`; 23 native theorems and 29 concrete definition/type targets are registered for the isolated package audit. `MaxwellEndpoint.U_zero` preserves the arbitrary harmonic mean. All 23 native theorems passed the isolated and integrated named audits. The exact conditional bridge remains A-tier; `FourierHodgeLaws` remains explicit.

[Integrated audit](../Auxillary/evidence/linux-43351199370/audit-summary.json) · [Isolated Maxwell audit](../Auxillary/evidence/linux-43351199370/standalone/audit-summary.json)

```text
INTEGRATED_LEAN_INPUT_HASHES = 37 / 37 MATCH
ISOLATED_LEAN_INPUT_HASHES = 7 / 7 MATCH
ISOLATED_SOURCE_FILES_VERIFIED = 18
ISOLATED_PROJECT_OBJECTS = INDEPENDENT
FORMAL_STATUS = CONDITIONAL_FORMAL_CLOSURE
```

## Adapter rename certificate

[Run 43353327242](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43353327242), source `8fd783b4d977fdb1a31cf4716023148ddfa26af9`: 226/226 integrated and 52/52 isolated audits passed; 37/37 integrated and 7/7 standalone Lean input hashes match. Both scopes reused trace-validated cached objects with zero module rebuilds. The 35 proof-module files remain byte-identical under the directory rename.

[Matching evidence](../Auxillary/evidence/linux-43353327242/).
