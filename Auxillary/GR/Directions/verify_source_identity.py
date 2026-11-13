#!/usr/bin/env python3
"""Check GR direction mirrors and the exact retained native source binding.

This script performs byte comparisons only. It does not execute Lean, Lake,
elan, or any compiler, and it does not promote the unresolved global target.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    repo = Path(__file__).resolve().parents[3]
    mapping = json.loads((repo / "Auxillary/GR/Directions/source-map.json").read_text())
    failures: list[str] = []

    for pair in mapping["files"]:
        for key in ("canonical", "mirror"):
            path = repo / pair[key]
            if not path.is_file():
                failures.append(f"Missing {key}: {pair[key]}")
            elif sha256(path) != pair["sha256"]:
                failures.append(f"Hash mismatch for {key}: {pair[key]}")

    manifest_path = repo / mapping["source_manifest"]
    if sha256(manifest_path) != mapping["source_manifest_sha256"]:
        failures.append("Retained source manifest hash mismatch")
    manifest = json.loads(manifest_path.read_text())
    if manifest["source_commit"] != mapping["proof_source_commit"]:
        failures.append("Retained proof-source commit mismatch")

    for entry in manifest["files"]:
        path = repo / entry["path"]
        if not path.is_file():
            failures.append(f"Missing certified input: {entry['path']}")
        elif sha256(path) != entry["sha256"]:
            failures.append(f"Certified input hash mismatch: {entry['path']}")

    result = {
        "status": "FAIL" if failures else "PASS",
        "mirror_pairs": len(mapping["files"]),
        "certified_inputs": len(manifest["files"]),
        "new_lean_declarations": mapping["new_lean_declarations"],
        "global_target_status": mapping["global_target_status"],
        "local_lean_lake_elan_executions": 0,
        "failures": failures,
    }
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
