# Auxillary

## Contents

| Path | Scope |
|---|---|
| [run.sh](run.sh) | Native Linux external build and fresh theorem audit |
| [run.cmd](run.cmd) | Historical native Windows entry point |
| [scripts/run.ps1](scripts/run.ps1) | Pinned dependency verification, cached compilation, source manifest, audit orchestration |
| [scripts/verify_audit.py](scripts/verify_audit.py) | Compiler provenance, source-hash, and approved-axiom verification |
| [audit-targets.txt](audit-targets.txt) | 174 exact registered declaration names |
| [cache-targets.txt](cache-targets.txt) | Pinned Mathlib cache target list |
| [formalization-status.json](formalization-status.json) | Exact theorem scope, explicit premises, external evidence, certification status |
| [CI_CACHE_AUDIT.txt](CI_CACHE_AUDIT.txt) | Cache design and recorded validation history |
| [evidence/](evidence/) | Original external compiler artifacts and provenance |

## External entry point

From the repository root, in the external native Linux environment:

```bash
bash Auxillary/run.sh
```

```text
COMPILER                    = LEAN_4.34.0-rc1_NATIVE_LINUX
CACHE_POLICY                = PRESERVE_COMPILER_DEPENDENCY_PROJECT_CACHES
THEOREM_AUDIT                = FRESH_174_NAMED_TARGETS
LOCAL_LEAN_EXECUTIONS        = 0
LEAN_INPUTS_UNCHANGED        = 30 / 30
PRIOR_CERTIFIED_SOURCE       = be8376a08573a7789e36b68c2bc48178aa6f53c3
PRIOR_CERTIFIED_RUN          = 43345557147
CURRENT_CERTIFIED_SOURCE     = b02425040a217a94855cfa52934e303f12fe80de
CURRENT_CERTIFIED_RUN        = 43348914489
FRESH_NAMED_AUDITS           = 174 / 174 PASS_STANDARD_ONLY
LAKE_FRESHNESS_EXIT          = 0
EXECUTED_MODULE_BUILDS       = 0
AUXILLARY_LAYOUT_VALIDATION = PASS_CACHED_NATIVE_LINUX_BUILD_AND174_FRESH_AUDITS
FORMAL_STATUS               = CONDITIONAL_FORMAL_CLOSURE
HODGE_LEAN_INHABITANT        = NOT_SUPPLIED
```

[Current native Linux run](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489) · [Audit summary](evidence/linux-43348914489/audit-summary.json) · [Original evidence](evidence/linux-43348914489/).

Compiler, dependency, and project caches were exact hits. Lake transitive traces validated reuse; all 174 named theorem audits executed fresh. The 38 original artifact files retain their source-manifest and provenance bytes.

## Root discovery boundary

`lakefile.lean`, `lake-manifest.json`, and `lean-toolchain` remain at the repository root for Lake and compiler discovery. `.github/workflows/` retains GitHub Actions discovery. `README.md`, `AGENTS.md`, `.gitignore`, and `.gitattributes` retain repository-wide indexing, instructions, and Git configuration.

The mathematical source roots remain [Fefferman_B_adapter/](../Fefferman_B_adapter/) and [B <-> Maxwell/](../B%20%3C-%3E%20Maxwell/). Evidence artifacts retain their original bytes and embedded historical paths. The `Auxillary/` relocation changes no Lean declaration, premise, or proof body.
