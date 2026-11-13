#!/usr/bin/env python3
"""Copy exact, pinned Git source objects into both standalone packages.

This program never invokes Lean, Lake, or elan, never edits an upstream checkout,
and never commits or pushes. A cache miss uses an isolated temporary Git checkout.
The original bytes of Git attribute/ignore files are retained with a .upstream
suffix so their rules cannot alter the containing repository's source snapshots.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tempfile


def git(root: Path, *args: str, data: bytes | None = None) -> bytes:
    return subprocess.run(
        ["git", "-C", str(root), *args], input=data, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).stdout


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob_id(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def safe_path(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or any(p in ("", ".", "..", ".git") for p in path.parts):
        raise ValueError(f"Unsafe upstream source path: {value!r}")
    return path


def stored_path(value: str) -> str:
    path = safe_path(value)
    return str(path.with_name(path.name + ".upstream")) if path.name in (".gitattributes", ".gitignore") else str(path)


def checkout_for(pin: dict, cache_root: Path, temporary: Path) -> Path:
    cached = cache_root / pin["name"]
    if (cached / ".git").exists():
        root = cached
    else:
        root = temporary / pin["name"]
        root.mkdir(parents=True)
        git(root, "init", "--quiet")
        git(root, "remote", "add", "origin", pin["url"])
        git(root, "fetch", "--quiet", "--depth=1", "origin", pin["rev"])
        git(root, "checkout", "--quiet", "--detach", "FETCH_HEAD")
    actual = git(root, "rev-parse", "HEAD").decode().strip()
    if actual != pin["rev"]:
        raise ValueError(f"Pinned revision mismatch for {pin['name']}: {actual}")
    if git(root, "status", "--porcelain", "--untracked-files=no").strip():
        raise ValueError(f"Tracked dependency source edits: {pin['name']}")
    return root


def git_entries(root: Path) -> list[dict]:
    entries = []
    for record in git(root, "ls-tree", "-rz", "--full-tree", "HEAD").split(b"\0"):
        if not record:
            continue
        fields, name = record.split(b"\t", 1)
        mode, kind, sha = fields.decode().split()
        path = name.decode("utf-8")
        if kind != "blob" or mode not in ("100644", "100755", "120000"):
            raise ValueError(f"Unsupported upstream object: {path}: {mode} {kind}")
        if mode == "120000" and path.endswith(".lean"):
            raise ValueError(f"Native Lean symlink requires explicit module handling: {path}")
        stored = stored_path(path) + (".upstream-symlink" if mode == "120000" else "")
        entries.append({"source_path": path, "path": stored, "mode": mode,
                        "stored_mode": "100644" if mode == "120000" else mode, "git_blob": sha})
    if len({e["path"] for e in entries}) != len(entries):
        raise ValueError("Snapshot filename collision")
    return sorted(entries, key=lambda e: e["source_path"])


def blobs(root: Path, entries: list[dict]):
    # Bounded batches avoid holding an entire upstream repository in memory.
    for start in range(0, len(entries), 200):
        batch = entries[start:start + 200]
        result = git(root, "cat-file", "--batch", data="".join(e["git_blob"] + "\n" for e in batch).encode())
        offset = 0
        for entry in batch:
            end = result.index(b"\n", offset)
            sha, kind, size_text = result[offset:end].decode().split()
            size = int(size_text)
            offset = end + 1
            raw = result[offset:offset + size]
            offset += size
            if sha != entry["git_blob"] or kind != "blob" or blob_id(raw) != sha or result[offset:offset + 1] != b"\n":
                raise ValueError(f"Invalid Git object stream: {entry['source_path']}")
            offset += 1
            yield entry, raw
        if offset != len(result):
            raise ValueError("Extra bytes in Git object stream")


def write_object(destination: Path, entry: dict, raw: bytes) -> None:
    path = destination / entry["path"]
    path.parent.mkdir(parents=True, exist_ok=True)
    if entry["mode"] == "120000":
        target = raw.decode("utf-8")
        original = destination / entry["source_path"]
        if Path(target).is_absolute() or not (original.parent / target).resolve().is_relative_to(destination.resolve()):
            raise ValueError(f"External upstream symlink: {entry['source_path']}")
    if path.is_symlink():
        raise ValueError(f"Unexpected destination symlink: {path}")
    if path.exists() and path.read_bytes() != raw:
        raise ValueError(f"Existing snapshot source mismatch: {path}")
    path.write_bytes(raw)
    path.chmod(0o755 if entry["stored_mode"] == "100755" else 0o644)


def materialize(repo: Path, cache_root: Path, report: Path) -> dict:
    lock = json.loads((repo / "lake-manifest.json").read_text())
    pins = sorted(lock["packages"], key=lambda p: p["name"])
    if len(pins) != 9 or any(p["type"] != "git" or p.get("subDir") for p in pins):
        raise ValueError("Expected the exact nine pinned Git dependencies")
    packages = [repo / "Fefferman_adapter", repo / "Maxwell_Endpoint"]
    toolchain = (repo / "lean-toolchain").read_text().strip()
    records = []
    with tempfile.TemporaryDirectory(prefix="nse-native-source-checkouts-") as temporary:
        for pin in pins:
            source = checkout_for(pin, cache_root, Path(temporary))
            entries = git_entries(source)
            destinations = [p / "NativeSources" / pin["name"] for p in packages]
            for destination in destinations:
                destination.mkdir(parents=True, exist_ok=True)
            total = 0
            for entry, raw in blobs(source, entries):
                entry["bytes"] = len(raw)
                entry["sha256"] = digest(raw)
                total += len(raw)
                for destination in destinations:
                    write_object(destination, entry, raw)
            record = {
                "name": pin["name"], "url": pin["url"], "revision": pin["rev"],
                "tree": git(source, "rev-parse", "HEAD^{tree}").decode().strip(),
                "commit_raw_base64": base64.b64encode(git(source, "cat-file", "commit", "HEAD")).decode(),
                "root": "NativeSources/" + pin["name"],
                "file_count": len(entries), "lean_file_count": sum(e["source_path"].endswith(".lean") for e in entries),
                "source_bytes": total, "files": entries,
            }
            records.append(record)
            print(json.dumps({k: record[k] for k in ("name", "revision", "file_count", "lean_file_count", "source_bytes")}), flush=True)
    methlib_manifests = [p / "NativeSources/methlib/SOURCE_MANIFEST.json" for p in packages]
    if methlib_manifests[0].read_bytes() != methlib_manifests[1].read_bytes():
        raise ValueError("The two Methlib source manifests differ")
    manifest = {
        "schema_version": 1,
        "kind": "COMPLETE_PINNED_NATIVE_DEPENDENCY_SOURCES",
        "toolchain": toolchain,
        "compiler_sources": "Init, Lean, Std and Lake are supplied by the exact pinned compiler distribution.",
        "snapshot_policy": "All tracked files of all nine dependency repositories; native source bytes and upstream Git trees are preserved. Git attribute/ignore basenames carry .upstream to neutralize containing-repository rules. Three ancillary symlink payloads are inert .upstream-symlink files; hydration restores original modes and paths.",
        "packages": records,
        "methlib": {
            "root": "NativeSources/methlib", "manifest": "NativeSources/methlib/SOURCE_MANIFEST.json",
            "revision": "e9cf90726b8544a268469ebc8fa6634e9c713e07",
            "manifest_sha256": digest(methlib_manifests[0].read_bytes()),
        },
    }
    raw_manifest = (json.dumps(manifest, ensure_ascii=False, indent=2) + "\n").encode()
    for package in packages:
        (package / "native-sources.json").write_bytes(raw_manifest)
    result = {
        "status": "PASS", "toolchain": toolchain,
        "packages": [p.name for p in packages], "dependency_count_per_package": len(records),
        "dependency_files_per_package": sum(p["file_count"] for p in records),
        "dependency_lean_files_per_package": sum(p["lean_file_count"] for p in records),
        "dependency_source_bytes_per_package": sum(p["source_bytes"] for p in records),
        "methlib_native_modules_per_package": 39,
        "native_sources_manifest_sha256": digest(raw_manifest),
        "upstream_repositories_modified": False,
        "lean_lake_elan_executions": 0,
    }
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps(result, indent=2) + "\n")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    print(json.dumps(materialize(root, (args.dependency_cache or root / ".lake/packages").resolve(), args.report.resolve()), indent=2))


if __name__ == "__main__":
    main()
