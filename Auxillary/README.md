# Auxillary

## Contents

| Path | Scope |
|---|---|
| [run.sh](run.sh) | Integrated native Linux build and fresh declaration audit |
| [run.cmd](run.cmd) | Historical repository Windows entry point |
| [scripts/run.ps1](scripts/run.ps1) | Pinned dependency verification, cached compilation, source manifests |
| [scripts/verify_audit.py](scripts/verify_audit.py) | Exact named axioms, compiler provenance, and source-hash verification |
| [scripts/isolate_maxwell_endpoint.py](scripts/isolate_maxwell_endpoint.py) | Independent Fefferman/Maxwell package isolation and source verification |
| [audit-targets.txt](audit-targets.txt) | 236 exact integrated audit targets |
| [cache-targets.txt](cache-targets.txt) | Pinned Mathlib cache target list |
| [formalization-status.json](formalization-status.json) | Exact theorem scope, explicit premises, external certification |
| [CI_CACHE_AUDIT.txt](CI_CACHE_AUDIT.txt) | Cache design and validation history |
| [evidence/](evidence/) | Original compiler artifacts and provenance |

## External execution

```bash
bash Auxillary/run.sh
```

The independent [Maxwell package](../Maxwell_Endpoint/) contains its own native runner. CI additionally compiles an isolated copy containing only that package and the pinned mathematical dependencies.

```text
COMPILER = LEAN_4.34.0-rc1_NATIVE_LINUX
INTEGRATED_AUDIT_TARGETS = 236
ISOLATED_FEFFERMAN_AUDIT_TARGETS = 236
ISOLATED_MAXWELL_AUDIT_TARGETS = 62
NATIVE_MAXWELL_THEOREMS = 23
CURRENT_VALIDATION = PENDING_NATIVE_SOURCE_PACKAGE_AUDITS
LOCAL_LEAN_EXECUTIONS = 0
HODGE_LEAN_INHABITANT = NOT_SUPPLIED
```

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
