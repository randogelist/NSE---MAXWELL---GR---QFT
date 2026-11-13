EXACT NATIVE L1 SOURCE EXPORT
Entry: L1_native.lean. Definitions and theorem bodies remain in their original modules.
Exact source status: L1_native_A_TIER.txt; export alone never promotes that status.
Source identity: source-map.json; complete export hashes: source-manifest.json.
External prerequisites: native Windows Lean/Lake 4.34.0-rc1, Git, Python >=3.10.
Command: run.cmd
Existing .lake objects and download caches are preserved and checked incrementally.
Missing pinned dependencies and official Mathlib cache entries are fetched normally.
No clean, forced cache replacement, lake update, or local authoring-time Lean execution.
Every run creates a separate artifacts/windows/<run-id>/ evidence directory.
Compilation is followed by a fresh root signature and standard-only axiom audit.
Source export alone does not establish A_TIER; review exact premises separately.
