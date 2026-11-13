#!/usr/bin/env python3
"""Export the GR source package and sibling audit runner for native Windows/Linux.

No Lean, Lake, elan, compiler cache, network request or Git mutation is executed.
The archive is a source deliverable, never new compilation evidence. The caller's
source commit is recorded as provenance; file SHA-256 values identify its bytes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

EXCLUDED_PARTS = {".lake", ".git", "__pycache__", "artifacts", "exports", "evidence"}
SUFFIXES = {".lean", ".json", ".md", ".txt", ".cmd", ".sh", ".py"}
RESERVED_WINDOWS = {"CON", "PRN", "AUX", "NUL"} | {
    f"{prefix}{index}" for prefix in ("COM", "LPT") for index in range(1, 10)
}


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_windows_path(value: str) -> None:
    path = PurePosixPath(value)
    require(not path.is_absolute() and str(path) == value and bool(path.parts),
            f"Invalid archive path: {value}")
    for part in path.parts:
        require(part not in {".", ".."} and not part.endswith((".", " ")),
                f"Unsafe path component: {part}")
        require(not re.search(r'[<>:"\\|?*\x00-\x1f]', part),
                f"Windows-incompatible path component: {part}")
        require(part.split(".", 1)[0].upper() not in RESERVED_WINDOWS,
                f"Reserved Windows component: {part}")


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def export(repo: Path, output: Path, source_commit: str) -> dict:
    require(re.fullmatch(r"[a-f0-9]{40}", source_commit) is not None,
            "A complete lowercase 40-digit source commit is required")
    repo = repo.resolve()
    output = output.resolve()
    package = repo / "GR_adapter"
    support = repo / "Auxillary" / "GR"
    require(package.is_dir() and support.is_dir(), "GR source package/support directory missing")
    source_paths = {
        p for p in package.rglob("*") if p.is_file()
        and not set(p.relative_to(package).parts) & EXCLUDED_PARTS
        and (p.suffix in SUFFIXES or p.name == "lean-toolchain")
    }
    source_paths.update((support / "scripts").glob("*.py"))
    source_paths.update({support / "audit-targets.json", support / "formalization-status.json"})
    require(all(p.is_file() and not p.is_symlink() for p in source_paths),
            "All exported inputs must exist as ordinary source files")
    required = {
        "GR_adapter/GRAdapter.lean", "GR_adapter/NSEGRForward.lean",
        "GR_adapter/NSEGRReverse.lean", "GR_adapter/lakefile.lean",
        "GR_adapter/lake-manifest.json", "GR_adapter/lean-toolchain",
        "GR_adapter/run.cmd", "GR_adapter/run.sh",
        "Auxillary/GR/scripts/run_gr.py", "Auxillary/GR/audit-targets.json",
        "Auxillary/GR/formalization-status.json",
    }
    entries: dict[str, tuple[bytes, int]] = {}
    for path in sorted(source_paths):
        name = path.relative_to(repo).as_posix()
        safe_windows_path(name)
        entries[name] = (path.read_bytes(), stat.S_IMODE(path.stat().st_mode))
    require(required <= entries.keys(), "Export is missing required package or audit inputs")
    folded = [name.casefold() for name in entries]
    require(len(set(folded)) == len(folded), "Case-insensitive archive path collision")

    lock = json.loads(entries["GR_adapter/lake-manifest.json"][0])
    dependencies = []
    for package_entry in lock["packages"]:
        revision = package_entry["rev"]
        require(package_entry["type"] == "git" and re.fullmatch(r"[a-f0-9]{40}", revision) is not None,
                "Dependency is not pinned to an immutable Git revision")
        url = package_entry["url"]
        require(url.startswith("https://github.com/"), "Expected a recorded public GitHub dependency")
        source_url = url.removesuffix(".git") + "/tree/" + revision
        dependencies.append({"name": package_entry["name"], "repository_url": url,
                             "revision": revision, "source_url": source_url})
    entries["GR_adapter/DEPENDENCY_SOURCE_POINTERS.json"] = (json_bytes({
        "compiler": entries["GR_adapter/lean-toolchain"][0].decode("utf-8").strip(),
        "dependency_sources": dependencies,
        "dependency_objects": "REUSE_ONLY_MATCHING_NATIVE_PLATFORM_AND_COMPILER_CACHES",
        "source_acquisition": "PINNED_LOCKFILE; EXTERNAL_RUNNER_ON_CACHE_MISS",
        "compiler_execution_during_export": False,
    }), 0o644)
    entries["EXPORT_README.txt"] = ((
        "NSE_GR_SOURCE_EXPORT\n"
        "WINDOWS_ENTRYPOINT = GR_adapter\\run.cmd\n"
        "LINUX_ENTRYPOINT = bash GR_adapter/run.sh\n"
        "REQUIRED_EXTERNAL_TOOLS = native Lean 4.34.0-rc1; Git; Python >= 3.9\n"
        "LAYOUT = GR_adapter + Auxillary/GR sibling directories\n"
        "CHECKOUT_OF_WINDOWS_INCOMPATIBLE_REPOSITORY_DIRECTORIES = NOT_REQUIRED\n"
        "DEPENDENCIES = exact GR_adapter/lake-manifest.json revisions\n"
        "DEPENDENCY_SOURCE_POINTERS = GR_adapter/DEPENDENCY_SOURCE_POINTERS.json\n"
        "CACHES = preserve compatible external native caches; never clean\n"
        "SOURCE_COMMIT_METADATA = caller-declared; file bytes separately SHA256-indexed\n"
        "STATUS = source export; no new compiler or theorem-audit evidence\n"
        "ADMISSION_PREMISES = unchanged; read Auxillary/GR/formalization-status.json\n"
    ).encode("utf-8"), 0o644)
    manifest = {
        "schema_version": 1, "caller_declared_source_commit": source_commit,
        "status": "SOURCE_EXPORT_ONLY", "local_lean_execution": 0,
        "source_commit_byte_equality": "NOT_INFERRED_FROM_CALLER_METADATA",
        "files": [{"path": name, "sha256": sha256(data), "size": len(data)}
                  for name, (data, _) in sorted(entries.items())],
    }
    entries["EXPORT_MANIFEST.json"] = (json_bytes(manifest), 0o644)
    output.parent.mkdir(parents=True, exist_ok=True)
    require(output not in source_paths, "Output must not replace an input")
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, (data, mode) in sorted(entries.items()):
            safe_windows_path(name)
            info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | mode) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(output) as archive:
        require(archive.testzip() is None, "Archive CRC check failed")
        for item in manifest["files"]:
            require(sha256(archive.read(item["path"])) == item["sha256"],
                    "Archive byte verification failed: " + item["path"])
    return {"output": str(output), "sha256": sha256(output.read_bytes()),
            "files": len(entries), "windows_paths": "PASS", "zip_bytes": "PASS",
            "source_commit_metadata": source_commit, "local_lean_execution": 0}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    args = parser.parse_args()
    print(json.dumps(export(args.repo_root, args.output, args.source_commit), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
