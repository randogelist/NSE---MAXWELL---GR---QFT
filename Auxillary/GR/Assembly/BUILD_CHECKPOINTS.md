# GR assembly: compiled-object checkpoints

## Invariants

```
proof-source delta = 0
theorem-signature delta = 0
allowed axioms = {propext, Classical.choice, Quot.sound}
object-cache hit != theorem certificate
current-source Lake validation -> fresh exact #check / #print axioms
local Lean execution = prohibited
```

## Retention

| Layer | Stored objects | Identity |
|---|---|---|
| Compiler | `~/.elan` | OS, architecture, exact toolchain |
| Dependencies | `.lake/packages`, `.mathlib-download-cache` | Pinned manifest; revision and working-tree verification |
| Assembly | `ASSEMBLY/.lake/build` | OS, architecture, configuration, source commit, run ID, attempt |
| Recoverable artifact | Entire assembly build directory, including hidden files and `ci-checkpoint.json` | `gr-assembly-build-RUN_ID-ATTEMPT`; 30 days |
| Fresh evidence | Compiler/source provenance, generated audit source, logs, named records | `gr-assembly-native-linux-SHA-ATTEMPT`; 30 days |

```
configuration = hash(ASSEMBLY/{lean-toolchain,lakefile.lean,lake-manifest.json})
cache key = nse-gr-assembly-checkpoint-v2-OS-ARCH-CONFIG-SHA-RUN-ATTEMPT
restore order:
  1. same CONFIG + same SHA
  2. same CONFIG
  3. legacy v1 + same CONFIG
save condition = verified dependencies + existing compiled objects
save outcome = success OR partial proof failure
```

Distinct run/attempt suffixes preserve newly compiled objects on same-source
retries. Automatic cache retention remains subject to GitHub eviction; the
separate downloadable artifact supplies explicit recovery within its retention.

## External execution

```bash
bash ASSEMBLY/run.sh --phase build --dag-build --batch-audits \
  --individual-modules --keep-going --source-commit "$GITHUB_SHA"
```

```
initial DAG:
  exit 0 -> all requested modules current
  nonzero -> explicit current successes and failures only

remaining eligible modules:
  exclude explicit failures and their dependency closure
  one batched Lake build
  exit 0 -> every requested target current
  nonzero -> individual current-build validation

fresh audit:
  imports = successfully validated modules only
  targets = identical fully qualified inventory
  commands = one #check + one #print axioms per target
  accept = exit 0 AND exactly one named axiom record per target
           AND axioms subset {propext, Classical.choice, Quot.sound}
  batch failure -> discard batch result -> fresh individual audits

summary:
  each stage -> actual shared audit-source hash + actual shared log hash
  any failed/blocked stage -> PARTIAL_STANDARD_ONLY; process exit 1
  cached object alone -> no promotion
```

Omitting `--batch-audits` retains the prior individual audit execution mode.

## Explicit recovery

Workflow: `Cached accelerated GR dependency build and exact audits`.

| Manual workflow input | Value |
|---|---|
| `checkpoint_run_id` | Run containing `gr-assembly-build-RUN_ID-ATTEMPT` |
| `checkpoint_attempt` | Artifact attempt; default `1` |

```
trusted same-repository assembly run on codex/gr-adapter
  -> artifact download -> CONFIG/OS/ARCH/toolchain equality checks
                  -> rsync --ignore-existing into restored build directory
                  -> current-source DAG build
                  -> fresh exact theorem audits
```

An empty `checkpoint_run_id` selects automatic cache recovery only. Explicit
artifact recovery preserves the current source commit. A failed historical run
may supply successful independent compiled modules; its failure status remains
recorded in `ci-checkpoint.json` and confers no theorem status.

## Trigger scope

```
ASSEMBLY-only changes -> assembly workflow
GR adapter inputs    -> GR workflow + consuming assembly workflow
Maxwell inputs       -> Maxwell workflow + any consuming adapter workflows
manual dispatch      -> retained for each workflow
```

## Baseline evidence

```
source = 8b542cd0b2500e701c127b197089937fdb7f31c1
run = 43492708971
compiler = Lean 4.34.0-rc1 / 3447a668783dbce1a8fdb97101dd067687b2b418
mathlib = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
audited targets = 1415 / 1549
failed modules = 4
blocked modules = 9
status = PARTIAL_STANDARD_ONLY

recorded build-phase command duration = 280.607 s
  initial DAG = 51.778 s
  18 repeated stage builds = 63.633 s
  52 fresh audit processes = 165.094 s
  other commands = 0.102 s
```

Optimization measurement requires subsequent matching-source external evidence.
These baseline values exclude cache transfer, runner setup, and artifact upload.

## Evidence verification

```bash
python Auxillary/GR/Assembly/scripts/verify_assembly.py \
  --repository-root "$GITHUB_WORKSPACE" \
  --evidence-directory "$GITHUB_WORKSPACE/Auxillary/GR/Assembly/evidence-current" \
  --source-commit "$GITHUB_SHA" --allow-partial
```

```
verification scope = current source bytes + exact target partition
                   + current build commands + fresh raw named axiom records
--allow-partial = explicit partial-evidence acceptance; no full-root promotion
default = full PASS_STANDARD_ONLY required
original failed build step = retained as failure
```

## Orchestration verification

```bash
python -m unittest discover -s Auxillary/GR/Assembly/scripts -p 'test_*.py'
```

```
test scope = audit parsing + target validation + build failure propagation
Lean/Lake execution by tests = 0
formal promotion by Python tests = 0
```
