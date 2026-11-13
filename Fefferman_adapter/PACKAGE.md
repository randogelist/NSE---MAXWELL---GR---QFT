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
AUDIT_TARGETS = 236
STATUS = A_TIER_CANDIDATE_FOR_CURRENT_ISOLATED_PACKAGE
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
METHLIB_TARGET_AUDIT_STATUS = A_TIER_CANDIDATE
```

## Exact mathematical scope

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED :
  NSEMaxwell.Bridge.FourierHodgeLaws →
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
ANALYTICITY_PREMISE = absent

UNRESOLVED_FOURIER_HODGE_FIELDS = {
  reconstruct_velocity,
  reconstruct_curl,
  canonical_smoothness,
  electric_hodge
}

FOURIER_HODGE_INHABITANT = NOT_SUPPLIED
ARBITRARY_DATA_FEFFERMAN_B = NOT_PROVED
ARBITRARY_DATA_MAXWELL_B = NOT_PROVED
UNCONDITIONAL_EXACT_EQUIVALENCE = NOT_PROVED
```

The 39-module Methlib closure supports ten separately audited endpoint declarations. Their native compilation does not identify the source's adjusted mean-zero proposition with the frozen arbitrary-mean target and does not discharge the four Hodge fields.

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
