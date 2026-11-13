# Native quantum obligations

Verified source: `3c2a8f5435b4e95e779222b37637f12a57d1eea9`. External run [43469332973](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43469332973) passed all 77 modules, 581 theorems, and 679 declaration audits. P1--P7 and `QuantumAdapter.Obligations.NSE_B_IFF_CANONICAL_QUANTUM` use only `propext`, `Classical.choice`, and `Quot.sound`. The root equivalence has no remaining adapter premise. P5 uses the universal constant 512; the stronger constant 16 is not certified here. The full original CI artifact and exact endpoint logs are retained under `evidence/3c2a8f5435b4e95e779222b37637f12a57d1eea9/`.

Compiler: `leanprover/lean4:v4.34.0-rc1`, external native Linux CI or native Windows replay.
Mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

`module-targets.json` and `audit-targets.txt` enumerate the exact registered
declarations, including public definitions and abbreviations; theorem counts
are recorded separately. `prepare_targets.py` inspects source only and never executes Lean.
Use `--module QuantumAdapter.Obligations.NAME` repeatedly to select a ready
batch; all selected obligation dependencies must also be selected.

`run.sh` reuses pinned dependency preparation and incremental Lake objects.
The default batch runner requests all selected modules in one cached Lake
build. Candidate completions receive a successful aggregate `--no-build`
transitive freshness check before they can enter the fresh combined
`#check` / `#print axioms` audit. A failed aggregate freshness check falls back
to individual checks. A failed aggregate audit promotes no declaration.
Independent module failures do not stop other Lake build jobs. Per-module
compiler and audit extracts, compiled-object SHA256 values, and complete
aggregate logs are retained. `--build-mode serial` preserves the previous
one-module build/audit fallback.
Evidence binds the exact source commit, every tracked proof-source blob,
compiler, dependency revisions, theorem names, and permitted standard axioms.

Audit success does not identify a conditional helper theorem with P1--P7.
An obligation is closed only after review of its exact native signature and
all displayed premises, with matching external compilation and axiom evidence.
The obligation ledger remains pending until that review is recorded.

External user replay from an existing checkout:

```sh
bash Auxillary/run.sh -Phase Dependencies
NSE_QUANTUM_OBLIGATIONS_EXTERNAL_NATIVE=1 bash Auxillary/quantum/obligations/run.sh
```

Native Windows replay requires Git, Python 3.10+, and the pinned native Lean
compiler on PATH. `run.cmd` invokes `windows.py`: existing dependencies and
project objects are reused, missing official Windows Mathlib cache objects are
fetched, and `run.py` performs the same exact theorem/axiom checks.

The repository's literal `B <-> ...` paths are invalid on Windows. Create a
sparse checkout containing the obligation closure and its configuration:

```cmd
git clone --no-checkout --branch codex/quantum-adapter-from-maxwell https://github.com/randogelist/NSE---MAXWELL---GR---QFT.git QuantumObligations
cd QuantumObligations
git sparse-checkout init --no-cone
git sparse-checkout set "/lean-toolchain" "/lakefile.lean" "/lake-manifest.json" "/.gitattributes" "/.github/" "/Auxillary/" "/Quantum_adapter/" "/Fefferman_adapter/" "/Maxwell_Endpoint/"
git checkout
Auxillary\quantum\obligations\run.cmd
```

Windows replay materializes the original arrow-directory Git blobs under
commit-specific safe paths. The original `lakefile.lean` stays unchanged;
`lake --file` selects a separately generated configuration containing exactly
four `srcDir` replacements. Each mapped source retains its original module
name and exact Git blob/SHA256. `source-layout.json` records the mapping, and
the audit independently recomputes it before compilation. Thus the complete
Closure import graph is supported without theorem-source changes.

For a standalone archive preserving this directory layout, place
`replay-source.json` beside `run.cmd`, `windows.py`, and `windows_layout.py`:

```json
{"repository":"https://github.com/randogelist/NSE---MAXWELL---GR---QFT.git",
 "source_commit":"<40-character immutable proof commit>"}
```

If the archive has no Git checkout, the launcher creates `replay-checkout`
under the archive root, fetches precisely that commit, and performs the sparse
checkout above before staging the safe source layout. An existing checkout
at a different commit is rejected. Repeated runs reuse its native caches.
The command `--repo-root PATH` selects an existing exact Git checkout.

Reports are separate under `artifacts/external-windows`; Linux evidence is
never relabeled as Windows evidence. The Windows launcher is source-prepared;
its runtime status requires an external native Windows replay.

The separate diagnostic workflow elaborates a temporary concatenation of
original candidate bodies with explicit per-file scopes and a source-line
map. Internal imports are removed; no admissions, axioms, or stub bodies are
inserted. Ordinary Lean error recovery may produce cascading diagnostics.
These results never establish A_TIER; the concatenated diagnostic emits no object files.
Its timeout applies only to the independent diagnostic process group.
No local Lean execution is part of the preparation workflow.
