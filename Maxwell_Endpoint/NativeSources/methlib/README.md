# Native Methlib source closure

```text
UPSTREAM = randogelist/Methlib
COMMIT = e9cf90726b8544a268469ebc8fa6634e9c713e07
UPSTREAM_PACKAGE = regularity-B-assembly/Singular-Axiomatic-closure
NATIVE_MODULES = 39
NATIVE_SOURCE_BYTES = 324890
UPSTREAM_SOURCE_MODIFICATIONS = 0
NAMESPACE = SingularClosure
SELECTED_ENDPOINTS = T01–T10
```

`SingularClosure/` contains the complete native source import closure of the
selected Fourier endpoints. `SOURCE_MANIFEST.json` records every original
upstream path, Git blob identifier, SHA256 hash, direct import and module order.
The containing package provides `MethlibEndpoints.lean`,
`MethlibEndpoints/Audit.lean`, `methlib-audit-targets.txt` and
`methlib-module-order.json`.

## Compiler configuration

```text
ORIGINAL_COMPILER = Lean 4.33.0
ORIGINAL_MATHLIB = db584cd6d46c92f209a44c0f1c829460d327499d
TARGET_COMPILER = Lean 4.34.0-rc1
TARGET_MATHLIB = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
```

`upstream/` preserves the original package configuration as provenance. The
containing adapter's configuration selects the active target compiler and
Mathlib. Matching external compilation and named axiom-audit records determine
certification; the source copy itself establishes no A-tier result.

## Exact scope

The source declarations retain the `SingularClosure` namespace. Source
`Fefferman_B_0_adjust` and `AX6Statement` remain separate definitions. The frozen
arbitrary-mean `NSEMaxwell.Classical.FeffermanB` statement is unchanged. None of
`reconstruct_velocity`, `reconstruct_curl`, `canonical_smoothness` or
`electric_hodge` is discharged by this source package.

## Source notices

Original source bytes and notices are preserved. `LICENSE_STATUS.md` records
the upstream licensing metadata; `third_party/leray-hopf-LICENSE` preserves the
source package's included third-party license.
