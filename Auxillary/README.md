# Auxillary

## Contents

| Path | Scope |
|---|---|
| [run.sh](run.sh) | Integrated native Linux build and fresh declaration audit |
| [run.cmd](run.cmd) | Historical repository Windows entry point |
| [scripts/run.ps1](scripts/run.ps1) | Pinned dependency verification, cached compilation, source manifests |
| [scripts/verify_audit.py](scripts/verify_audit.py) | Exact named axioms, compiler provenance, and source-hash verification |
| [scripts/isolate_maxwell_endpoint.py](scripts/isolate_maxwell_endpoint.py) | Independent Fefferman/Maxwell package isolation and source verification |
| [audit-targets.txt](audit-targets.txt) | 400 exact integrated audit targets |
| [cache-targets.txt](cache-targets.txt) | Pinned Mathlib cache target list |
| [formalization-status.json](formalization-status.json) | Exact theorem scope, explicit premises, external certification |
| [CI_CACHE_AUDIT.txt](CI_CACHE_AUDIT.txt) | Cache design and validation history |
| [evidence/](evidence/) | Original compiler artifacts and provenance |

## External execution

```bash
bash Auxillary/run.sh
```

The independent [Fefferman package](../Fefferman_adapter/) and [Maxwell package](../Maxwell_Endpoint/) contain native runners. CI compiles each isolated package from its contained source closure with pinned dependencies and fresh theorem audits.

```text
COMPILER = LEAN_4.34.0-rc1_NATIVE_LINUX
INTEGRATED_AUDIT_TARGETS = 400
ISOLATED_FEFFERMAN_AUDIT_TARGETS = 400
ISOLATED_MAXWELL_AUDIT_TARGETS = 62
NATIVE_MAXWELL_THEOREMS = 23
CURRENT_VALIDATION = PASS_THREE_SCOPES
EXTERNAL_RUN = 43373061238
CERTIFIED_SOURCE = c4c7bcdca6e652905107bb1a3102ed50d94c2e6b
CANONICAL_ROOT = NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL
CURRENT_FORMAL_STATUS = UNCONDITIONAL_CLOSURE
LOCAL_LEAN_EXECUTIONS = 0
HODGE_LEAN_INHABITANT = NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant
HODGE_SOURCE_BYTE_IDENTITY = 19/19
HODGE_THEOREM_AUDITS = 163
NEW_CANONICAL_WRAPPER_AUDITS = 1
ARBITRARY_DATA_GLOBAL_EXISTENCE = OPEN
```

## Current integration certificate

[Run 43373061238](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43373061238), source `c4c7bcdca6e652905107bb1a3102ed50d94c2e6b`: 400/400 integrated, 400/400 isolated Fefferman, and 62/62 isolated Maxwell fresh audits passed with only `propext`, `Classical.choice`, and `Quot.sound`. [Matching evidence](../Auxillary/evidence/linux-43373061238) records source hashes, native compiler provenance, package isolation, and named axiom results.

The root type is `NSEMaxwell.Classical.ExactEquivalence`, with no analytic-law premise. The 19 Hodge source files match Methlib `f927f1e31196f0be71b2581dc85f6e3fd19e0746` byte-for-byte. Their 163 theorem audits and the one canonical wrapper audit extend the prior 236-target inventory to 400. Arbitrary-data global existence for either side remains open.

Compiler, dependency, compressed Mathlib, and project caches are retained. Exact pins and ordinary Lake transitive traces govern reuse; audit results are regenerated. Historical evidence below remains unchanged and applies only to its original runs and source commits.

## Prior auxiliary-layout certificate

[Run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489), source `b02425040a217a94855cfa52934e303f12fe80de`: 174/174 fresh audits; 30/30 matching Lean inputs; compiler, dependency and project cache exact hits; zero module rebuilds after Lake trace validation.

[Original evidence](evidence/linux-43348914489/) preserves all 38 artifact files and their historical source paths. The native Maxwell extraction has the separate matching certificate below.

## Root discovery boundary

`lakefile.lean`, `lake-manifest.json`, and `lean-toolchain` remain at the repository root. GitHub Actions discovery and repository-wide instructions/configuration retain their functional locations. Standalone Maxwell configuration and runners reside inside `Maxwell_Endpoint/` to permit independent extraction.

## Native Maxwell extraction certificate

[Run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370), source `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`: 226/226 integrated audits and 52/52 isolated Maxwell audits passed with approved foundational axioms only. All 37 integrated and seven standalone Lean input hashes match. The isolated compiler verified all 18 package files and shared only the pinned mathematical dependency cache.

[Original evidence](evidence/linux-43351199370/) preserves 109 artifact files. [Standalone audit](evidence/linux-43351199370/standalone/audit-summary.json) and [isolation result](evidence/linux-43351199370/maxwell-isolation-result.json) certify the native package independently of the NSE adapter.

## Adapter rename certificate

[Run 43353327242](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43353327242), source `8fd783b4d977fdb1a31cf4716023148ddfa26af9`: 226/226 integrated and 52/52 isolated audits passed; 37/37 integrated and 7/7 standalone Lean input hashes match. Both scopes reused trace-validated cached objects with zero module rebuilds. The 35 proof-module files remain byte-identical under the directory rename.

[Matching evidence](evidence/linux-43353327242/).
