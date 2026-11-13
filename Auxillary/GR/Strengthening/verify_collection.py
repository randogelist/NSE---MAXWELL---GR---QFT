#!/usr/bin/env python3
"""Verify the pinned GR strengthening source collection without invoking Lean."""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    repo = Path(__file__).resolve().parents[3]
    index = json.loads((Path(__file__).parent / "endpoint-index.json").read_text())
    sources = {r["id"]: r for r in index["sources"]}
    failures: list[str] = []
    expected_files: set[Path] = set()
    checked_sources: set[str] = set()
    seen: set[str] = set()

    for endpoint in index["endpoints"]:
        name = endpoint["endpoint"]
        if name in seen:
            failures.append(f"Duplicate endpoint: {name}")
        seen.add(name)
        directory = repo / endpoint["directory"]
        source = sources[endpoint["source_id"]]
        archived = directory / "Source.lean"
        wrapper = directory / "Endpoint.lean"
        expected_files.update((archived, wrapper))
        if not archived.is_file() or not wrapper.is_file():
            failures.append(f"Missing source/entrypoint: {name}")
            continue
        data = archived.read_bytes()
        if sha256(data) != source["sha256"] or git_blob(data) != source["git_blob_sha"]:
            failures.append(f"Source identity mismatch: {name}")
        if len(data) != source["bytes"]:
            failures.append(f"Source size mismatch: {name}")
        if not 1 <= endpoint["declaration_line"] <= len(data.decode().splitlines()):
            failures.append(f"Invalid declaration location: {name}")
        if source["id"] not in checked_sources and source.get("repository_snapshot_path"):
            canonical = repo / source["repository_snapshot_path"]
            if not canonical.is_file() or canonical.read_bytes() != data:
                failures.append(f"Canonical source mismatch: {source['module']}")
            checked_sources.add(source["id"])
        entry_data = wrapper.read_bytes()
        if sha256(entry_data) != endpoint["endpoint_sha256"]:
            failures.append(f"Entrypoint hash mismatch: {name}")
        lines = entry_data.decode().splitlines()
        required = [f"import {source['module']}", f"#check @{name}", f"#print axioms {name}"]
        if any(lines.count(line) != 1 for line in required):
            failures.append(f"Entrypoint import/query mismatch: {name}")
        if sorted(p.name for p in directory.iterdir()) != ["Endpoint.lean", "Source.lean"]:
            failures.append(f"Unexpected endpoint directory content: {name}")

    for pending in index["pending"]:
        directory = repo / pending["directory"]
        marker = directory / ".gitkeep"
        expected_files.add(marker)
        if not marker.is_file() or marker.read_bytes() != b"":
            failures.append(f"Pending placeholder mismatch: {pending['endpoint']}")
        elif sorted(p.name for p in directory.iterdir()) != [".gitkeep"]:
            failures.append(f"Unexpected pending implementation: {pending['endpoint']}")

    root = repo / "B <-> GR/Strengthening/Endpoints"
    actual_files = {p for p in root.rglob("*") if p.is_file()}
    if actual_files != expected_files:
        failures.append("Endpoint-tree file coverage mismatch")
    kinds = dict(Counter(r["kind"] for r in index["endpoints"]))
    if kinds != {"Native": 104, "Methlib": 36, "Mathlib": 43}:
        failures.append("Expected endpoint-category coverage mismatch")
    if len(index["endpoints"]) != 183 or len(index["pending"]) != 24 or len(sources) != 79:
        failures.append("Expected endpoint/source/pending counts mismatch")
    print(json.dumps({
        "status": "FAIL" if failures else "PASS_SOURCE_IDENTITY",
        "endpoints": len(index["endpoints"]), "by_kind": kinds,
        "unique_sources": len(sources), "pending_constructions": len(index["pending"]),
        "source_copies": len(index["endpoints"]), "entrypoint_files": len(index["endpoints"]),
        "local_lean_lake_elan_executions": 0,
        "compiler_or_axiom_audit_performed": False, "failures": failures,
    }, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
