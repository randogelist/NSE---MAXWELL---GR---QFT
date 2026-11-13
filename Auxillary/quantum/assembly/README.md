# External assembly validation

Compiler: `leanprover/lean4:v4.34.0-rc1`, native Linux.
Mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

```bash
python3 Auxillary/quantum/assembly/prepare_targets.py
```

The preparation command performs static inspection only. Review its exact
`audit-targets.txt` and `module-targets.json` before committing. Public top-level
`theorem` and `lemma` commands are selected; private declarations and definitions
are excluded. Add any further exact declarations explicitly to both files.
New files under `QuantumAdapter/Assembly/` are included automatically; the root
`QuantumAdapter.Assembly` is included last when present. Empty modules are reported.

External execution after restoring the existing compiler/dependency/project caches:

```bash
bash Auxillary/run.sh -Phase Dependencies
NSE_QUANTUM_ASSEMBLY_EXTERNAL_NATIVE=1 bash Auxillary/quantum/assembly/run.sh
```

GitHub Actions supplies the external context automatically. Other invocations
require the explicit external opt-in. `run.cmd` launches this same procedure in
the external user's WSL/Linux environment; it does not claim a native Windows
checkout of paths containing `<` and `>`.

Only matching successful dependency preparation is required. Integrated and
standalone audits remain separate final validation scopes. The runner verifies
the exact compiler, dependency lock revisions, preparation fingerprint, Git
source blobs and SHA-256 source manifest. Cached Lake objects are reused through
ordinary `lake build --no-build` freshness checks and incremental `lake build`.
No cache cleanup or forced cache download occurs.

Each module is attempted independently even after another module fails. Each
successful module receives a fresh audit importing that module and issuing one
`#check @name` and one `#print axioms name` per explicit target. Failed builds are
never audited using stale objects. Missing, duplicated, unexpected, malformed,
`sorryAx`, or unapproved axiom records fail the aggregate audit. Only `propext`,
`Classical.choice`, and `Quot.sound` are approved. Semantic premise discharge is
never inferred from compilation or the axiom audit.

Outputs: `artifacts/external-linux/quantum-assembly/`, including per-module build
and audit logs, generated audit sources, `module-status.json`, `audit-summary.json`,
`source-manifest.json`, and `provenance.json`. A passing partial target selection
does not establish the final root; `root_module_included` records its presence.

Final proof promotion additionally requires the exact root scope/premise review
and all repository-mandated integrated and standalone validation scopes.
