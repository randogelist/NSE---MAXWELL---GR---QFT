# Contained native sources

```text
PINNED_DEPENDENCY_REPOSITORIES = 9
SOURCE_SCOPE = complete tracked snapshots
UPSTREAM_FILES_PER_PACKAGE = 9842
UPSTREAM_NATIVE_LEAN_FILES_PER_PACKAGE = 9515
UPSTREAM_SOURCE_BYTES_PER_PACKAGE = 114476228
NATIVE_METHLIB_CLOSURE = 39 modules
NATIVE_METHLIB_ENDPOINTS = 10
SOURCE_MANIFEST = native-sources.json
COMPILER_LIBRARIES = Init, Lean, Std, Lake from pinned Lean 4.34.0-rc1
```

Each dependency directory preserves every upstream native Lean source byte and module path. The manifest records upstream revisions, exact Git commit objects, original tree/blob identities, SHA256 hashes, modes and original-to-stored path mappings.

Original `.gitattributes` and `.gitignore` bytes are stored as `.gitattributes.upstream` and `.gitignore.upstream`. Three ancillary symbolic-link payloads are regular `.upstream-symlink` files. Source hydration restores original paths, file modes and internal links in the actual dependency checkouts. These storage mappings do not modify native Lean modules.

`scripts/hydrate_native_sources.py` at the package root reconstructs missing exact pinned Git checkouts from these sources. Existing valid dependency checkouts are retained. `scripts/verify_native_sources.py` verifies exact inventories, Git identities, active import closure and actual dependency source bytes. Compiled objects remain cached.

The `methlib` directory contains the complete selected `SingularClosure` import closure and original provenance. The independent native endpoint audits do not supply an inhabitant of the Fefferman–Maxwell analytic contract.
