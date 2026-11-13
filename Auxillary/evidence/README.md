# Fefferman adapter rename certificate

[Run 43353327242](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43353327242), source `8fd783b4d977fdb1a31cf4716023148ddfa26af9`: 226/226 integrated and 52/52 isolated audits passed; 37/37 integrated and 7/7 standalone Lean input hashes match. Both scopes reused trace-validated cached objects with zero module rebuilds. The 35 proof-module files remain byte-identical under the directory rename.

[linux-43353327242/](linux-43353327242/) preserves all73 original artifact files. [Integrated audit](linux-43353327242/audit-summary.json); [isolated audit](linux-43353327242/standalone/audit-summary.json).

```text
ARTIFACT_SHA256 = 58b473f212cb1ae8385edf4a2e1535ddc2feb7fb88f6f168fc668db3f4868924
INTEGRATED_MANIFEST_SHA256 = 8c685d3c9e3372fadc5ed36418a7a70e0c323d2c057c71da027d07c7de8c4316
STANDALONE_MANIFEST_SHA256 = c11c4f17a5bf5826e0545332038e408d7c2080c2ccb4b16657bce3973481f7f5
LOCAL_LEAN_EXECUTIONS = 0
```

## Historical certificates

# Native Maxwell package and integrated bridge certificate

[Run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370) compiled the native package and the complete repository using external native Linux Lean 4.34.0-rc1. Source commit: `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`.

| Scope | Fresh named audits | Matching Lean inputs |
|---|---:|---:|
| Integrated repository | 226/226 PASS_STANDARD_ONLY | 37/37 |
| Isolated Maxwell package | 52/52 PASS_STANDARD_ONLY | 7/7 |

[linux-43351199370/](linux-43351199370/) preserves all 109 original artifact files. The isolated build verifies all 18 package sources, permits only Mathlib/MaxwellEndpoint imports, shares the pinned dependency cache, and keeps project objects separate. [Isolation result](linux-43351199370/maxwell-isolation-result.json).

```text
ARTIFACT_SHA256 = 4da8e2720886ff08fd905a6e3b94ec579dcf0027411bd07e2c275dc7d282a2fb
INTEGRATED_MANIFEST_SHA256 = 69abcd877f16956cce0b5fe0fc323465aded436bc8369aa674e86cee31a9445e
STANDALONE_MANIFEST_SHA256 = 489e25cd64350c06ca232223ceda96205194b071c72134fe0f8eb58f22eef322
NATIVE_THEOREMS = 23 A_TIER
EXACT_BRIDGE = CONDITIONAL_FORMAL_CLOSURE
HODGE_LEAN_INHABITANT = NOT_SUPPLIED
LOCAL_LEAN_EXECUTIONS = 0
```

Every certificate below retains its original source commit and historical input paths. Promotion records remain separate from original artifact bytes.

## Prior certificate indexes

# Auxillary evidence location

```text
ARTIFACT_RELOCATION          = BYTE_EXACT
LEAN_INPUTS_UNCHANGED        = 30 / 30
PRIOR_CERTIFIED_SOURCE       = be8376a08573a7789e36b68c2bc48178aa6f53c3
PRIOR_CERTIFIED_RUN          = 43345557147
CURRENT_CERTIFIED_SOURCE     = b02425040a217a94855cfa52934e303f12fe80de
CURRENT_CERTIFIED_RUN        = 43348914489
AUXILLARY_LAYOUT_VALIDATION = PASS_CACHED_NATIVE_LINUX_BUILD_AND174_FRESH_AUDITS
```

## Current Auxillary layout certificate

[linux-43348914489/](linux-43348914489/) preserves all 38 original files from [native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489).

```text
SOURCE_COMMIT = b02425040a217a94855cfa52934e303f12fe80de
BUILD = PASS
FRESH_THEOREM_AXIOM_AUDIT = 174 / 174 PASS_STANDARD_ONLY
LEAN_SOURCE_HASHES_MATCHING_DELIVERY = 30 / 30
VERIFIED_SOURCE_INPUTS = 289
COMPILER_DEPENDENCY_PROJECT_CACHES = EXACT_HITS
LAKE_FRESHNESS_EXIT = 0
BUILD_STRATEGY = LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE
EXECUTED_MODULE_BUILDS = 0
ARTIFACT_ID = 14003036770
ARTIFACT_SHA256 = 4d1bfce16808246fe1190bea523358dc0d150efafa0c7b59f338670b85df86df
SOURCE_MANIFEST_SHA256 = 1d230d04d0796b21b806b552b4bb9ca14debd25c00e65a75ef670cdf0477d6cd
FORMAL_STATUS = CONDITIONAL_FORMAL_CLOSURE
HODGE_INHABITANT = NOT_SUPPLIED
```

Certificate subdirectories preserve their original artifact bytes and embedded source paths. `Auxillary/run.cmd` has the expected CRLF checkout normalization. All Lean input hashes match directly. The prior certificates below identify their original source commits and runner layouts.

# Prior matching proof-source certificate

[linux-43345557147/](linux-43345557147/) contains all 65 original artifact files from [native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147).

```text
SOURCE_COMMIT = be8376a08573a7789e36b68c2bc48178aa6f53c3
BUILD = PASS
THEOREM_AXIOM_AUDIT = 174 / 174 PASS_STANDARD_ONLY
LEAN_SOURCE_HASHES_MATCHING_DELIVERY = 30 / 30
ARTIFACT_SHA256 = d33c336a8cef9758cdbf87f5b96ed9ad2dd6e5fdad84caf231b7b13e677b36ca
FORMAL_STATUS = CONDITIONAL_FORMAL_CLOSURE
HODGE_INHABITANT = NOT_SUPPLIED
```

All new directional endpoints and the reduced root have only the approved foundational axioms. Historical manifests retain their original paths. The run 43345557147 source manifest records the adapter and directional source paths before the auxiliary-file relocation. The runner's CRLF checkout normalization for `run.cmd` is governed by `.gitattributes`; all Lean source matches are byte-exact.

# External evidence after directory reorganization

The certificate subdirectories below retain their original artifact bytes.
Their embedded source-manifest paths describe the original source commit.
The active library now resides under `Fefferman_B_adapter/`; directional
proof bodies reside under `B <-> Maxwell/=>/` and `B <-> Maxwell/<=/`.

The matching cached native Linux build and 174-target audit passed in run
43345557147 for source commit be8376a08573a7789e36b68c2bc48178aa6f53c3. Historical source-manifest paths are not
rewritten inside certificate artifacts.

## Historical evidence inventory

# External compiler and theorem audit evidence

## Current certified Linux proof snapshot

```text
RUN = 43336709607
AUDITED_SOURCE = d241f2b700be66ab447cb1650770271e1b364b8a
COMPILER = Native Linux Lean 4.34.0-rc1
TARGET = x86_64-unknown-linux-gnu
COMPILER_COMMIT = 3447a668783dbce1a8fdb97101dd067687b2b418
BUILD = PASS
FRESH_THEOREM_AXIOM_AUDIT = PASS_STANDARD_ONLY
AUDITED_DECLARATIONS = 170 / 170
LEAN_SOURCE_HASHES_MATCH_DELIVERY = 25 / 25
PRESERVED_ORIGINAL_ARTIFACT_FILES = 60
LOCAL_LEAN_EXECUTIONS = 0
EXACT_REDUCED_ROOT = FourierHodgeLaws -> ExactEquivalence
FORMAL_STATUS = CONDITIONAL_FORMAL_CLOSURE
UNCONDITIONAL_EQUIVALENCE = NOT_PROVED
```

[Successful Linux workflow](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43336709607)

[Original Linux artifact](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43336709607/artifacts/13998740266)

```text
Artifact ZIP SHA256:
76c772bea8d3a9879bcb3ced03e6c60e128c5fac8601df0b0e94ae58dce46b6d
Source manifest SHA256:
2e170563a63e264960afcc7cfc9e4aed952ff209e029ca696f9b034687d597a5
```

All files under `linux-43336709607/` preserve original artifact bytes. This publication changes evidence and status documentation; the 25 audited Lean inputs remain byte-identical.

## Prior matching Windows proof snapshot

```text
RUN = 43333835295
AUDITED_SOURCE = 1bd2ee067d4aad3c265b32efd533ef270179e665
COMPILER = Native Windows Lean 4.34.0-rc1
BUILD = PASS
FRESH_THEOREM_AXIOM_AUDIT = PASS_STANDARD_ONLY
AUDITED_DECLARATIONS = 170 / 170
PROJECT_DECLARATIONS = 166
REGISTERED_MATHLIB_DECLARATIONS = 4
SOURCE_INPUT_VERIFICATION = PASS
LEAN_SOURCE_HASHES_MATCH_DELIVERY = 25 / 25
PRESERVED_ORIGINAL_ARTIFACT_FILES = 58
LOCAL_LEAN_EXECUTIONS = 0
EXACT_REDUCED_ROOT = FourierHodgeLaws -> ExactEquivalence
FORMAL_STATUS = CONDITIONAL_FORMAL_CLOSURE
UNCONDITIONAL_EQUIVALENCE = NOT_PROVED
```

[Successful workflow](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43333835295)

[Original artifact](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43333835295/artifacts/13995999237)

```text
Artifact ZIP SHA256:
0fb3739800b7d282576868d0b9b5fac4246b8c713c67c8ac7901cfb8dfd9fa47
Source manifest SHA256:
b3be4cfb54f92124268b4241625b8f60a3c66d9276179777223a388a46781628
```

All files in `windows-43333835295/` preserve the original artifact bytes. The artifact contains its pre-run scope declaration. Subsequent promotion records are separate. The user-requested Linux migration changes the external execution platform; its new compiler and audit evidence is recorded above.

## Historical 74-target snapshot

```text
RUN = 43318057281
AUDITED_SOURCE = 0b793e57271073fb3b0206dcad99a2797d5f8211
COMPILER = Native Windows Lean 4.34.0-rc1
BUILD = PASS
LEAN_AUDIT_COMMAND = PASS
THEOREM_AXIOM_AUDIT = PASS_STANDARD_ONLY
AUDITED_DECLARATIONS = 74
SOURCE_INPUT_VERIFICATION = PASS
LEAN_SOURCE_HASHES_MATCH_HISTORICAL_SNAPSHOT = 16 / 16
LOCAL_LEAN_EXECUTIONS = 0
```

The files in `windows-43318057281/` retain their original bytes. The evidence contains the pre-run declaration of scope; promotion is recorded separately after successful validation.

Exact root: `PeriodicAnalyticLaws → ExactEquivalence`. All nine analytic endpoints remain explicit and unresolved. No unconditional equivalence is certified.

[Successful workflow](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43318057281)

[Original artifact](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43318057281/artifacts/13990185678)

```text
Original ZIP SHA-256:
e5fc7ade2aed6f22c3deeb3a83170a6c53e72c317ab04647692a436f0f1b33e5

Source manifest SHA-256:
cf68016d6739febf4580ce6bec82a5955a2e274cfd0a2ce28b9ff28a94e23c52
```
