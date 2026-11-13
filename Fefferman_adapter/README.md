# Fefferman adapter

```text
CANONICAL_ROOT = NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL
CANONICAL_ROOT_TYPE = NSEMaxwell.Classical.ExactEquivalence
CURRENT_FORMAL_STATUS = UNCONDITIONAL_CLOSURE
EXTERNAL_RUN = 43373061238
CERTIFIED_SOURCE = c4c7bcdca6e652905107bb1a3102ed50d94c2e6b
REGISTERED_PACKAGE_AUDIT_TARGETS = 400
HODGE_SOURCE_BYTE_IDENTITY = 19/19
HODGE_THEOREM_AUDITS = 163
NEW_CANONICAL_WRAPPER_AUDITS = 1
ARBITRARY_DATA_GLOBAL_EXISTENCE = OPEN
```

## Exact Lean statement

The canonical theorem in [NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean](NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean) has type:

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL :
  NSEMaxwell.Classical.ExactEquivalence
```

```text
ExactEquivalence =
  ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
    (FeffermanB ν ↔ MaxwellB ν c)
```

The root has no `FourierHodgeLaws` or parameter-smoothing premise. Its concrete inhabitant is `NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant`. The original conditional root and both directional APIs retain their original types.

The [frozen target](NSEMaxwell/Classical.lean) remains unforced and periodic in three spatial dimensions, with arbitrary velocity mean, periodic pressure, and joint `ContDiffOn ℝ ∞` through `t = 0`. Negative-time values remain unrestricted. Exact equivalence is proved; arbitrary-data existence for `FeffermanB` and `MaxwellB` separately remains open.

## Standalone native package

[PACKAGE.md](PACKAGE.md) specifies independent extraction. The package contains the NSE adapter and Hodge proof sources, ten byte-identical Maxwell/directional copies under [LocalDependencies/](LocalDependencies/), complete Mathlib and eight companion snapshots under [NativeSources/](NativeSources/), and the original selected 39-module `SingularClosure` closure.

```bash
bash Fefferman_adapter/run.sh
```

`hydrate_native_sources.py` reconstructs missing exact pinned dependency checkouts from contained sources. Existing valid dependency checkouts and object caches are preserved. `verify_native_sources.py` checks source inventory, Git identities, compiler-source equality, and import closure. Extraction requires no parent-directory source dependency.

The 19 Hodge source files under [FourierHodgeLaws/](FourierHodgeLaws/) and [FourierHodgeLaws_inhabitant.lean](FourierHodgeLaws_inhabitant.lean) are byte-identical to Methlib source `f927f1e31196f0be71b2581dc85f6e3fd19e0746`. The audit inventory is the previous 236 declarations plus 163 Hodge theorems and one canonical wrapper.

## Proof components

| Path | Exact role |
|---|---|
| [NSEMaxwell/Classical.lean](NSEMaxwell/Classical.lean) | NSE solution, Fefferman-B proposition, exact equivalence definition |
| [NSEMaxwell/AnalyticContracts.lean](NSEMaxwell/AnalyticContracts.lean) | Magnetic paths and reusable analytic contracts |
| [NSEMaxwell/AnalyticReduction.lean](NSEMaxwell/AnalyticReduction.lean) | Four-field `FourierHodgeLaws` contract and reduction |
| [FourierHodgeLaws/SpatialInhabitant.lean](FourierHodgeLaws/SpatialInhabitant.lean) | Actual H1, H2, and H4 endpoints |
| [FourierHodgeLaws/ParameterSmoothing.lean](FourierHodgeLaws/ParameterSmoothing.lean) | Scalar/vector inverse-Laplacian smoothness on closed forward spacetime |
| [FourierHodgeLaws/CanonicalInhabitant.lean](FourierHodgeLaws/CanonicalInhabitant.lean) | H3 canonical smoothness |
| [FourierHodgeLaws/Inhabitant.lean](FourierHodgeLaws/Inhabitant.lean) | Concrete Hodge inhabitant and native exact equivalence |
| [NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean](NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean) | Canonical unconditional root and retained conditional APIs |
| [NSEMaxwell/Audit.lean](NSEMaxwell/Audit.lean) | Exact signatures and named axiom audit commands |
| [Endpoints/](Endpoints/) | Historical source snapshots, signatures, and original endpoint provenance |

[INTEGRATION_PLAN.md](../B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md) records the completed proof chain. [FOURIER_HODGE_COMPOSITION_B_TIER.txt](../B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt) retains the mathematical derivation. The 14 `.lean.txt` reference snapshots remain original source records; the current proof is the native compiled Hodge construction.

## Current external certificate

[Run 43373061238](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43373061238), source `c4c7bcdca6e652905107bb1a3102ed50d94c2e6b`: 400/400 integrated, 400/400 isolated Fefferman, and 62/62 isolated Maxwell fresh named audits passed. The only axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

[Matching evidence](../Auxillary/evidence/linux-43373061238) contains the compiler, source-manifest, package-isolation, and axiom-audit records. The exact canonical root has `UNCONDITIONAL_CLOSURE`; no unresolved certificate, witness, checker, admission, or analytic premise occurs in its proof route. This status concerns the equivalence, not a separate arbitrary-data global solution theorem.

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

[Integrated audit](../Auxillary/evidence/linux-43359539373/audit-summary.json) · [Fefferman audit](../Auxillary/evidence/linux-43359539373/fefferman-standalone/audit-summary.json) · [Retained evidence](../Auxillary/evidence/linux-43359539373/)

## Historical external certificates

[Native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147): build PASS; 174/174 named audits PASS_STANDARD_ONLY; 30/30 Lean input hashes matched that source snapshot. [Audit summary](../Auxillary/evidence/linux-43345557147/audit-summary.json). At that source, the conditional directions were A-tier and the Hodge inhabitant was deferred. The relocated auxiliary runner paths also passed [native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489), source `b02425040a217a94855cfa52934e303f12fe80de`: 174/174 fresh audits, 30/30 matching Lean inputs, and zero module rebuilds after Lake trace validation. [Retained audit summary](../Auxillary/evidence/linux-43348914489/audit-summary.json).

## Historical native extraction certificate: run 43351199370

```text
CERTIFICATE_RUN = 43351199370
CERTIFICATE_SCOPE = HISTORICAL_SOURCE_7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6
SOURCE_STATUS = A_TIER_FOR_EXACT_CONDITIONAL_BRIDGE
REGISTERED_ROOT_AUDIT_TARGETS = 226
REGISTERED_MAXWELL_AUDIT_TARGETS = 52
ROOT_EXTERNAL_VALIDATION = PASS_BUILD_AND226_FRESH_AUDITS
ISOLATED_MAXWELL_VALIDATION = PASS_BUILD_AND52_FRESH_AUDITS
HODGE_LEAN_INHABITANT = NOT_SUPPLIED
```

The native Maxwell package is upstream of this adapter in the import graph. The adapter and both implication directions retain their exact explicit hypotheses. Source extraction passed both external build and theorem-audit scopes in [run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370), source `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`.

Native witness endpoints: `MaxwellEndpoint.zero_solution` and `MaxwellEndpoint.zero_datum_global_instance`; 23 native theorems and 29 concrete definition/type targets are registered for the isolated package audit. `MaxwellEndpoint.U_zero` preserves the arbitrary harmonic mean. All 23 native theorems passed the isolated and integrated named audits. The bridge certified in run 43351199370 was A-tier with `FourierHodgeLaws` explicit.

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
