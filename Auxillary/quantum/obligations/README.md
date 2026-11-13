# Native quantum obligations

Compiler: `leanprover/lean4:v4.34.0-rc1`, external native Linux.
Mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

`module-targets.json` and `audit-targets.txt` enumerate the exact candidate
declarations. `prepare_targets.py` inspects source only and never executes Lean.
Use `--module QuantumAdapter.Obligations.NAME` repeatedly to select a ready
batch; all selected obligation dependencies must also be selected.

`run.sh` reuses pinned dependency preparation and incremental Lake objects.
Each selected module receives a cache freshness check, an incremental build
when required, and a fresh `#check` / `#print axioms` audit. Independent modules
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

`run.cmd` launches this same cached Linux replay through WSL.
No local Lean execution is part of the preparation workflow.
