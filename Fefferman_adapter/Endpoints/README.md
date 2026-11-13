# Copied Mathlib and Methlib endpoints

```text
SELECTED_DECLARATIONS = 22
CORE                 = 16
OPTIONAL             = 4
AUXILIARY            = 1
REFERENCE_ONLY       = 1
SOURCE_FILES         = 14
SOURCE_BYTES_CHANGED = 0
HODGE_SOURCE_PORTS   = DEFERRED
```

## Index

| File or directory | Content |
|---|---|
| [ENDPOINTS.json](ENDPOINTS.json) | Exact signatures, implicit contexts, imports, pins, hashes, adapters, and audit boundaries |
| [ENDPOINT_INDEX.md](ENDPOINT_INDEX.md) | Declaration-to-source map and direct upstream downloads |
| [sources/mathlib/](sources/mathlib/) | Six byte-exact selected Mathlib source files |
| [sources/methlib/](sources/methlib/) | Eight byte-exact selected Methlib source files |
| [SOURCES.md](SOURCES.md) | Provenance and dependency boundary |
| [SHA256SUMS](SHA256SUMS) | Current endpoint-folder checksums |
| [PRIOR_STAGING_CHECKS.json](PRIOR_STAGING_CHECKS.json) | Historical mathematical/static staging receipt at commit 2373ce37659fa2f84920da0e5a26652a124623b7 |
| [PRIOR_STAGING_SHA256SUMS](PRIOR_STAGING_SHA256SUMS) | Original staging checksums for the previous layout |

Mathematical composition: [FOURIER_HODGE_COMPOSITION_B_TIER.txt](../../B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt).

Future ports: [INTEGRATION_PLAN.md](../../B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md).

## Source status

The copied `.lean.txt` files contain complete original Lean source bytes. The suffix keeps references outside the active module graph. The pinned cached Mathlib dependency supplies active Mathlib declarations. Methlib proofs originate from Lean 4.33.0 and require exact transport and external target-compiler audits before use in the new Hodge inhabitant.

Retained named target audits cover M01, M02, M05, and M07. Source presence does not transfer a theorem-level audit to another compiler context. Copying endpoints does not discharge the four analytic fields.

## Pins

```text
Target Lean     = leanprover/lean4:v4.34.0-rc1
Mathlib         = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
Methlib         = e9cf90726b8544a268469ebc8fa6634e9c713e07
Methlib Lean    = leanprover/lean4:v4.33.0
Methlib Mathlib = db584cd6d46c92f209a44c0f1c829460d327499d
```
