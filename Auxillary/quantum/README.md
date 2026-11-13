# Quantum external validation

```text
Compiler                  = leanprover/lean4:v4.34.0-rc1
Platform                  = external native Linux
Mathlib                   = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
Local Lean executions     = prohibited
Dependency cache          = verified inherited repository preparation
Project cache             = Lake transitive trace verification
Audit output reuse        = prohibited
Allowed axioms            = propext, Classical.choice, Quot.sound
Promotion                 = exact scope and premise review after matching evidence
```

```bash
bash Auxillary/run.sh -Phase Dependencies
bash Auxillary/run.sh -Phase BuildAudit
NSE_QUANTUM_EXTERNAL_NATIVE=1 bash Auxillary/quantum/run.sh
```

GitHub Actions supplies the external-runner context automatically. The runner
rejects other local invocations before Lean, Lake, or Git subprocess execution.

`module-order.json` is an ordered array of objects:

```json
{
  "module": "QuantumAdapter.Phase",
  "path": "Quantum_adapter/QuantumAdapter/Phase.lean",
  "stage": "adapter"
}
```

Stage order is `adapter → forward → reverse → assembly`. Every listed module
must have an actual source file and a registered Lake library. Names are unique.
Each stage uses one ordinary incremental Lake invocation. Within a stage, Lake
schedules independent targets according to its native dependency graph; the next
stage starts only after the current stage succeeds. No cleaning operation occurs.

`audit-targets.txt` lists exact existing declarations, one per line.
`formalization-status.json` records the exact implemented scope and all remaining
analytic, semantic, witness, certificate and admission premises.

The generated `QuantumAudit.lean` imports every scheduled module and executes
`#check @declaration` and `#print axioms declaration` once per selected target.
The inherited exact axiom parser rejects missing, duplicated, malformed or
unapproved axiom records. Matching input bytes are checked against the current
Git commit and SHA-256 hashes before and after compilation.

Outputs reside in `artifacts/external-linux/quantum/`: compiler identity,
dependency identity, source manifest, per-stage logs, fresh type/axiom output,
provenance, and audit summary. The parent artifact also retains the matching
inherited integrated audit and source closure.

```text
PASS_STANDARD_ONLY
  => selected declarations compiled with approved foundational axioms
  != discharge of displayed theorem hypotheses
  != construction of the unresolved full quantum generator
  != universal Navier–Stokes regularity
```


## Native analytic assembly

`QuantumAdapter.Assembly`: 203 additional declarations in 13 modules.
Exact source: `1a0664fc219e6b4e2caf005384bd71b585ad0847`.
External compiler and fresh theorem-level standard-axiom audit: PASS.

[Current exact root and premise index](assembly/exports/exact_quantum_root_for_canonical_flow_A_TIER.txt)
· [Assembly replay](assembly/README.md)
· [Assembly evidence](assembly/evidence/1a0664fc219e6b4e2caf005384bd71b585ad0847/).

The original 204-target adapter audit remains separately reproducible.
The native assembly constructs complete phase orbits, projection bounds,
Gaussian moments, transport/domain adapters, and quantitative packet estimates.
Seven explicit dynamical/continuum endpoints remain in the canonical root.
