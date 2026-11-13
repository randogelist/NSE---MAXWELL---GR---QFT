# Fefferman native package

```text
PACKAGE = fefferman_adapter
COMPILER = leanprover/lean4:v4.34.0-rc1
MATHLIB = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
ENTRY_POINT_LINUX = bash run.sh
ENTRY_POINT_WINDOWS = run.cmd
DEPENDENCY_POLICY = exact pinned Git checkouts; official incremental cache reuse
SOURCE_MANIFEST = native-sources.json
PROJECT_COPY_MANIFEST = local-project-sources.json
AUDIT_TARGETS = 400
STATUS = UNCONDITIONAL_CLOSURE_FOR_EXACT_EQUIVALENCE
EXTERNAL_RUN = 43373061238
CERTIFIED_SOURCE = c4c7bcdca6e652905107bb1a3102ed50d94c2e6b
```

## Package source roots

| Library | Package-local source root |
|---|---|
| `NSEMaxwell` | `.` |
| `MaxwellEndpoint` | `LocalDependencies/Maxwell` |
| `NSEMaxwellForward` | `LocalDependencies/Forward` |
| `NSEMaxwellReverse` | `LocalDependencies/Reverse` |
| `SingularClosure` | `NativeSources/methlib` |
| `MethlibEndpoints` | `.` |
| `FourierHodgeLaws` | `.` |
| `FourierHodgeLaws_inhabitant` | `.` |

All library paths are internal to this directory. The ten native Maxwell/directional copies are byte-checked against their canonical repository modules during isolation. The complete pinned native Mathlib and subordinate dependency sources are inventoried by `native-sources.json`; compilation uses the equal-byte verified dependency cache. The selected Methlib import closure is compiled as `SingularClosure` under the target compiler.

## Complete upstream source snapshots

```text
NativeSources/mathlib
NativeSources/batteries
NativeSources/Qq
NativeSources/aesop
NativeSources/proofwidgets
NativeSources/importGraph
NativeSources/LeanSearchClient
NativeSources/plausible
NativeSources/Cli
```

Each of these nine directories contains every tracked file of its exact pinned upstream repository, including its native `.lean` sources, package configuration, licenses, and accompanying assets. `native-sources.json` records original paths, stored paths, file modes, Git blob identities, SHA256 hashes, byte counts, upstream revisions, and upstream tree identities.

```text
UPSTREAM_NATIVE_SOURCE_BYTES = preserved
UPSTREAM_NATIVE_MODULE_PATHS = preserved
UPSTREAM_GIT_METADATA_BASENAME_MAP = {
  .gitattributes -> .gitattributes.upstream,
  .gitignore -> .gitignore.upstream
}
UPSTREAM_GIT_METADATA_BYTES = preserved
ANCILLARY_SYMLINK_STORAGE = original_link_payload_in_regular_.upstream-symlink_file
HYDRATION = restores_original_paths_modes_blobs_trees_and_commits
SNAPSHOT_GIT_TREE = different_path_layout_due_to_metadata_renames
RECORDED_UPSTREAM_TREE = exact_original_Git_tree_identity
COMPILER_PROVIDED_SOURCES = {Init, Lean, Std, Lake}
```

The metadata renames prevent copied Git rules from changing the containing repository's byte handling or tracked source inventory. Three ancillary upstream symbolic links are stored as inert regular files containing their original link payloads; their stored names append `.upstream-symlink`. No native `.lean` module is renamed. Source hydration reconstructs the exact pinned Git commits and original file modes in `.lake/packages`, using the contained source objects and retaining existing correct caches. Compiler-provided libraries remain part of the exact pinned compiler distribution. Complete source containment includes upstream tests and ancillary files; the external compiler and named axiom audit certify the selected native import graph and declaration inventory.

```text
NativeSources/methlib = complete_39_module_import_closure_for_10_selected_endpoints
METHLIB_UPSTREAM = randogelist/Methlib@e9cf90726b8544a268469ebc8fa6634e9c713e07
METHLIB_ORIGINAL_COMPILER = Lean 4.33.0
METHLIB_TARGET_COMPILER = Lean 4.34.0-rc1
METHLIB_TARGET_AUDIT_STATUS = PASS_10_SELECTED_ENDPOINTS_RUN_43359539373
```

## Integrated Hodge source

```text
HODGE_UPSTREAM = randogelist/Methlib@f927f1e31196f0be71b2581dc85f6e3fd19e0746
HODGE_SOURCE_FILES = 19
HODGE_SOURCE_BYTE_IDENTITY = 19/19
HODGE_THEOREM_AUDITS = 163
CANONICAL_WRAPPER_AUDITS = 1
AUDIT_COUNT = 236 + 163 + 1 = 400
```

The 19 Hodge files are distinct from the older 39-module `SingularClosure` closure. The original Hodge proofs retain their exact source bytes and namespace. The canonical repository wrapper imports the actual inhabitant; it does not add a law premise or replace a frozen definition.

## Exact mathematical scope

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL :
  NSEMaxwell.Classical.ExactEquivalence
```

```text
ExactEquivalence =
  ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
    (FeffermanB ν ↔ MaxwellB ν c)

DIMENSION = 3
DOMAIN = unit-periodic Euclidean fields
FORCING = zero
VELOCITY_MEAN = arbitrary
PRESSURE = periodic
REGULARITY = joint C-infinity through t = 0
NEGATIVE_TIME_VALUES = unrestricted
ANALYTICITY_PREMISE = absent
FOURIER_HODGE_INHABITANT = NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant
UNRESOLVED_ROOT_ANALYTIC_PREMISES = NONE
UNCONDITIONAL_EXACT_EQUIVALENCE = PROVED
ARBITRARY_DATA_FEFFERMAN_B = OPEN
ARBITRARY_DATA_MAXWELL_B = OPEN
```

The original conditional APIs remain unchanged. The source's adjusted mean-zero propositions are distinct from the frozen arbitrary-mean target and are not used as substitutes. The unconditional canonical root proves an equivalence between existence statements; it does not independently establish either existence statement.

## Current external certificate

[Run 43373061238](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43373061238), source `c4c7bcdca6e652905107bb1a3102ed50d94c2e6b`, passed the 400 integrated, 400 isolated Fefferman, and 62 isolated Maxwell named audits with standard axioms only. [Matching evidence](../Auxillary/evidence/linux-43373061238) records the exact source hashes, compiler, and standalone verification results. The prior 236-target certificate remains scoped to run 43359539373.

## External execution

```sh
bash run.sh -SourceCommit <40-hex-source-commit> -ReportDirectory <absolute-report-directory>
```

An attached Git checkout supplies the source commit automatically; an isolated copy accepts the explicit original commit. Each successful execution verifies the compiler, source hydration, all nine dependency revisions, source containment, ordinary Lake transitive traces, fresh signatures, and fresh named axiom records. Cached objects are reused only after freshness verification. Isolated packages reconstruct independent dependency source checkouts and may share the verified compiled dependency objects.

```text
ALLOWED_AXIOMS = {propext, Classical.choice, Quot.sound}
PREPARED_SOURCE ≠ A_TIER
MATCHING_EXTERNAL_COMPILER_AND_AXIOM_AUDIT ⇒ eligibility_for_A_TIER
AXIOM_AUDIT ⇏ analytic_premise_discharge
```
