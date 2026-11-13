#!/usr/bin/env python3
"""Restore exact pinned dependency Git checkouts from contained native sources.

No Lean, Lake, elan, network download, cache deletion, or upstream modification is
performed. Existing matching checkouts remain untouched. Missing checkouts are
assembled atomically from verified Git objects; optional links reuse only each
matching dependency's compiled .lake/build directory.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tempfile
import zlib


HEX40 = re.compile(r"[a-f0-9]{40}\Z")
HEX64 = re.compile(r"[a-f0-9]{64}\Z")
MODES = {"100644", "100755", "120000"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def safe_relative(value: str) -> PurePosixPath:
    require(isinstance(value, str) and value and "\\" not in value,
            f"Invalid relative source path: {value!r}")
    path = PurePosixPath(value)
    require(not path.is_absolute() and str(path) == value and
            all(part not in {"", ".", "..", ".git"} for part in path.parts),
            f"Unsafe relative source path: {value!r}")
    return path


def git(root: Path, *arguments: str) -> bytes:
    return subprocess.run(["git", "-C", str(root), *arguments], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def object_bytes(kind: str, raw: bytes) -> bytes:
    return kind.encode("ascii") + b" " + str(len(raw)).encode("ascii") + b"\0" + raw


def object_id(kind: str, raw: bytes) -> str:
    return hashlib.sha1(object_bytes(kind, raw)).hexdigest()


def write_object(git_dir: Path, kind: str, raw: bytes) -> str:
    encoded = object_bytes(kind, raw)
    oid = hashlib.sha1(encoded).hexdigest()
    path = git_dir / "objects" / oid[:2] / oid[2:]
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        require(zlib.decompress(path.read_bytes()) == encoded, "Git object collision or corruption.")
    else:
        path.write_bytes(zlib.compress(encoded))
    return oid


def tree_objects(entries: list[dict]) -> tuple[str, dict[str, bytes]]:
    root: dict = {}
    seen: set[str] = set()
    for entry in entries:
        path = safe_relative(entry["source_path"])
        require(str(path) not in seen, f"Duplicate upstream source path: {path}")
        seen.add(str(path))
        mode, oid = entry["mode"], entry["git_blob"]
        require(mode in MODES and isinstance(oid, str) and HEX40.fullmatch(oid) is not None,
                f"Invalid Git source entry: {path}")
        node = root
        for part in path.parts[:-1]:
            if part not in node:
                node[part] = {}
            require(isinstance(node[part], dict), f"Git file/directory collision: {path}")
            node = node[part]
        require(path.name not in node, f"Git file/directory collision: {path}")
        node[path.name] = (mode, oid)
    objects: dict[str, bytes] = {}

    def encode(node: dict) -> str:
        records: list[tuple[bytes, bytes]] = []
        for name, value in node.items():
            name_bytes = name.encode("utf-8")
            if isinstance(value, dict):
                mode, oid = "40000", encode(value)
                order = name_bytes + b"/"
            else:
                mode, oid = value
                order = name_bytes
            records.append((order, mode.encode("ascii") + b" " + name_bytes + b"\0" + bytes.fromhex(oid)))
        raw = b"".join(record for _, record in sorted(records))
        oid = object_id("tree", raw)
        objects[oid] = raw
        return oid

    return encode(root), objects


def validate_record(record: dict, pin: dict) -> tuple[bytes, dict[str, bytes]]:
    require(record["name"] == pin["name"] and record["url"] == pin["url"] and
            record["revision"] == pin["rev"], "Native dependency pin mismatch.")
    safe_relative(record["root"])
    revision, tree = record["revision"], record["tree"]
    require(HEX40.fullmatch(revision) is not None and HEX40.fullmatch(tree) is not None,
            "Invalid native dependency Git identity.")
    entries = record["files"]
    require(isinstance(entries, list) and entries and len(entries) == record["file_count"],
            "Native dependency file inventory is empty or inconsistent.")
    stored: set[str] = set()
    for entry in entries:
        path = str(safe_relative(entry["path"]))
        require(path not in stored, "Duplicate stored native source path.")
        stored.add(path)
        require(isinstance(entry["bytes"], int) and entry["bytes"] >= 0 and
                HEX64.fullmatch(entry["sha256"]) is not None, "Invalid native source byte identity.")
    calculated_tree, objects = tree_objects(entries)
    require(calculated_tree == tree, "Native source inventory does not reconstruct the pinned Git tree.")
    raw = base64.b64decode(record["commit_raw_base64"], validate=True)
    require(object_id("commit", raw) == revision, "Native commit object differs from the pinned revision.")
    require(raw.startswith(b"tree " + tree.encode("ascii") + b"\n"),
            "Native commit object points to a different source tree.")
    return raw, objects


def source_bytes(package: Path, record: dict, entry: dict) -> bytes:
    directory = package / str(safe_relative(record["root"]))
    source = directory / str(safe_relative(entry["path"]))
    # Inert stored symlink blobs and original symlink snapshots are both encoded
    # by the original Git blob. Hydrated checkouts restore original Git modes.
    raw = os.readlink(source).encode("utf-8") if source.is_symlink() else source.read_bytes()
    require(len(raw) == entry["bytes"] and hashlib.sha256(raw).hexdigest() == entry["sha256"] and
            object_id("blob", raw) == entry["git_blob"],
            f"Bundled source identity differs: {record['name']}/{entry['path']}")
    return raw


def restore_worktree(target: Path, path: PurePosixPath, mode: str, raw: bytes) -> None:
    destination = target / str(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if mode == "120000":
        link = raw.decode("utf-8")
        require(link and not Path(link).is_absolute() and
                (destination.parent / link).resolve().is_relative_to(target.resolve()),
                f"Escaping native dependency symlink: {path}")
        destination.symlink_to(link)
    else:
        destination.write_bytes(raw)
        destination.chmod(0o755 if mode == "100755" else 0o644)


def attach_compiled_objects(target: Path, record: dict, compiled_root: Path | None) -> bool:
    if compiled_root is None:
        return False
    cached = compiled_root / record["name"]
    require(cached.is_dir() and (cached / ".git").exists(),
            f"Verified compiled dependency checkout is absent: {record['name']}")
    require(git(cached, "rev-parse", "HEAD").decode().strip() == record["revision"],
            f"Compiled dependency revision mismatch: {record['name']}")
    require(not git(cached, "status", "--porcelain", "--untracked-files=no").strip(),
            f"Compiled dependency checkout contains tracked modifications: {record['name']}")
    build = cached / ".lake/build"
    if not build.is_dir():
        return False
    destination = target / ".lake/build"
    require(not destination.exists() and not destination.is_symlink(),
            "Native dependency snapshot unexpectedly contains a build directory.")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.symlink_to(build.resolve(), target_is_directory=True)
    return True


def restore_dependency(package: Path, dependencies: Path, record: dict, pin: dict,
                       compiled_root: Path | None) -> dict:
    raw_commit, trees = validate_record(record, pin)
    name = record["name"]
    require(re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None, "Invalid dependency name.")
    destination = dependencies / name
    require(not destination.is_symlink(), f"Dependency source directory is linked: {name}")
    if (destination / ".git").exists():
        actual = git(destination, "rev-parse", "HEAD").decode().strip()
        require(actual == record["revision"], f"Existing dependency revision mismatch: {name}")
        return {"name": name, "revision": actual, "tree": record["tree"],
                "status": "REUSED_WITHOUT_MODIFICATION", "source_downloads": 0,
                "compiled_objects_linked": (destination / ".lake/build").is_symlink()}
    require(not destination.exists() or destination.is_dir() and not any(destination.iterdir()),
            f"Nonempty dependency directory has no Git identity: {name}")
    temporary = Path(tempfile.mkdtemp(prefix=f".native-{name}-", dir=dependencies))
    try:
        git(temporary, "init", "--quiet", "--template=", "--initial-branch=snapshot")
        git(temporary, "config", "core.autocrlf", "false")
        git(temporary, "config", "core.filemode", "true")
        git(temporary, "config", "core.symlinks", "true")
        git(temporary, "remote", "add", "origin", record["url"])
        git_dir = temporary / ".git"
        for entry in record["files"]:
            raw = source_bytes(package, record, entry)
            require(write_object(git_dir, "blob", raw) == entry["git_blob"], "Git blob reconstruction failed.")
            restore_worktree(temporary, safe_relative(entry["source_path"]), entry["mode"], raw)
        for oid, raw in trees.items():
            require(write_object(git_dir, "tree", raw) == oid, "Git tree reconstruction failed.")
        require(write_object(git_dir, "commit", raw_commit) == record["revision"],
                "Git commit reconstruction failed.")
        (git_dir / "shallow").write_text(record["revision"] + "\n", encoding="ascii")
        git(temporary, "update-ref", "refs/heads/snapshot", record["revision"])
        git(temporary, "symbolic-ref", "HEAD", "refs/heads/snapshot")
        git(temporary, "read-tree", "HEAD")
        require(git(temporary, "rev-parse", "HEAD^{tree}").decode().strip() == record["tree"],
                "Hydrated Git tree differs from the pinned source tree.")
        require(not git(temporary, "status", "--porcelain", "--untracked-files=no").strip(),
                "Hydrated native source worktree is not byte-equivalent to Git HEAD.")
        linked = attach_compiled_objects(temporary, record, compiled_root)
        # Rename preserves an existing nonempty directory rather than replacing it.
        temporary.rename(destination)
        return {"name": name, "revision": record["revision"], "tree": record["tree"],
                "status": "RESTORED_FROM_CONTAINED_NATIVE_SOURCES", "source_downloads": 0,
                "source_files_verified": len(record["files"]), "compiled_objects_linked": linked}
    finally:
        if temporary.exists():
            # Only this invocation's unpublished temporary construction is removed.
            shutil.rmtree(temporary)


def hydrate(package: Path, dependencies: Path, compiled_root: Path | None = None) -> dict:
    require(package.is_dir(), "Native package root is absent.")
    require(not dependencies.is_symlink(), "Dependency source root must not be a symlink.")
    dependencies.mkdir(parents=True, exist_ok=True)
    manifest_path = package / "native-sources.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    lock = json.loads((package / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["toolchain"] == (package / "lean-toolchain").read_text().strip(),
            "Native source compiler pin mismatch.")
    pins = {pin["name"]: pin for pin in lock["packages"]}
    records = {record["name"]: record for record in manifest["packages"]}
    require(len(records) == len(manifest["packages"]) == len(pins) == len(lock["packages"]) == 9 and
            set(records) == set(pins) and all(pin["type"] == "git" and not pin.get("subDir") for pin in pins.values()),
            "Expected exactly the nine pinned native Git dependencies.")
    if compiled_root is not None:
        require(compiled_root.resolve() != dependencies.resolve(), "Source and compiled cache roots coincide.")
    output = [restore_dependency(package, dependencies, records[name], pins[name], compiled_root)
              for name in sorted(records)]
    return {"schema_version": 1, "status": "PASS", "package_root": str(package),
            "dependency_root": str(dependencies),
            "native_sources_manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
            "dependency_count": len(output), "dependencies": output,
            "dependency_source_downloads": 0, "shared_source_checkouts": False,
            "compiled_cache_root": str(compiled_root) if compiled_root is not None else None,
            "lean_lake_elan_executions": 0}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True)
    parser.add_argument("--compiled-cache-root", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    try:
        # Check the supplied root itself before resolving parent path components.
        require(not args.dependency_root.is_symlink(), "Dependency source root is linked.")
        result = hydrate(args.package_root.resolve(), args.dependency_root.absolute(),
                         args.compiled_cache_root.resolve() if args.compiled_cache_root else None)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        result = {"schema_version": 1, "status": "FAIL", "error": str(error),
                  "dependency_source_downloads": 0, "lean_lake_elan_executions": 0}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
