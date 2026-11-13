# Native quantum obligations

Compiler: `leanprover/lean4:v4.34.0-rc1`, external native Linux CI or native Windows replay.
Mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

`module-targets.json` and `audit-targets.txt` enumerate the exact candidate
declarations. `prepare_targets.py` inspects source only and never executes Lean.
Use `--module QuantumAdapter.Obligations.NAME` repeatedly to select a ready
batch; all selected obligation dependencies must also be selected.

`run.sh` reuses pinned dependency preparation and incremental Lake objects.
Each selected module receives one cached `lake build`, which validates
transitive source freshness and rebuilds only stale objects, followed by a fresh
`#check` / `#print axioms` audit. Independent modules
are attempted after unrelated failures; dependent failures are recorded.
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

Windows evidence records the omitted arrow files by their exact Git blobs.
The selected project import closure must avoid those files; an attempted
arrow-module import fails explicitly. No theorem source is rewritten.
Reports are separate under `artifacts/external-windows`; Linux evidence is
never relabeled as Windows evidence. The Windows launcher is source-prepared;
its runtime status requires an external native Windows replay.
No local Lean execution is part of the preparation workflow.
