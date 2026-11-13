#!/usr/bin/env python3
"""Seed missing standalone project artifacts from a matching audited root build.

Only physical copies of module artifacts are created. Existing cache files are
never overwritten. Ordinary Lake freshness validation and a fresh standalone
axiom audit remain mandatory; this program never invokes Lean, Lake, or elan.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


PACKAGES = {"Maxwell_Endpoint": "maxwell", "Fefferman_adapter": "fefferman"}
ARTIFACT = re.compile(r"\.(?:olean|ilean|c|bc|o|trace|setup)(?:\.[A-Za-z0-9_-]+)*\Z")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git(repo: Path, *arguments: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *arguments], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True).stdout.strip()


def safe_relative(value: str) -> Path:
    path = Path(value)
    require(isinstance(value, str) and value and not path.is_absolute() and
            ".." not in path.parts and "\\" not in value and path.as_posix() == value,
            f"Invalid relative source path: {value!r}")
    return path


def regular_files(root: Path, *, exclude_lake: bool = False) -> dict[str, Path]:
    require(root.is_dir() and not root.is_symlink(), f"Expected an independent directory: {root}")
    result: dict[str, Path] = {}
    for directory, directories, names in os.walk(root, followlinks=False):
        base = Path(directory)
        if exclude_lake and base == root:
            directories[:] = [name for name in directories if name != ".lake"]
        for name in directories:
            require(not (base / name).is_symlink(), f"Linked directory in cache/source inventory: {base / name}")
        for name in names:
            path = base / name
            require(path.is_file() and not path.is_symlink(), f"Linked or nonregular cache/source file: {path}")
            result[path.relative_to(root).as_posix()] = path
    return result


def module_roots(package: str, *, canonical: bool) -> dict[str, str]:
    if canonical:
        roots = {"MaxwellEndpoint": "Maxwell_Endpoint", "MethlibEndpoints": "Fefferman_adapter",
                 "SingularClosure": "Fefferman_adapter/NativeSources/methlib"}
        if package == "Fefferman_adapter":
            roots.update({"NSEMaxwell": "Fefferman_adapter", "NSEMaxwellForward": "B <-> Maxwell/=>",
                          "NSEMaxwellReverse": "B <-> Maxwell/<="})
    else:
        roots = {"MethlibEndpoints": "", "SingularClosure": "NativeSources/methlib"}
        if package == "Maxwell_Endpoint":
            roots["MaxwellEndpoint"] = ""
        else:
            roots.update({"NSEMaxwell": "", "MaxwellEndpoint": "LocalDependencies/Maxwell",
                          "NSEMaxwellForward": "LocalDependencies/Forward",
                          "NSEMaxwellReverse": "LocalDependencies/Reverse"})
    return roots


def module_sources(paths: set[str], package: str) -> dict[str, str]:
    result = {}
    for namespace, prefix in module_roots(package, canonical=False).items():
        stem = (prefix + "/" if prefix else "") + namespace
        for relative in paths:
            if relative == stem + ".lean" or relative.startswith(stem + "/") and relative.endswith(".lean"):
                module_path = relative[len(prefix) + 1:] if prefix else relative
                module = module_path[:-5].replace("/", ".")
                require(module not in result, f"Duplicate standalone module: {module}")
                result[module] = relative
    require(result, "Standalone project module inventory is empty.")
    return result


def module_for_artifact(relative: str) -> str | None:
    if relative.startswith("lib/lean/"):
        remainder = relative[len("lib/lean/"):]
    elif relative.startswith("ir/"):
        remainder = relative[len("ir/"):]
    else:
        return None
    path = Path(remainder)
    stem, separator, suffix = path.name.partition(".")
    if not separator or ARTIFACT.fullmatch("." + suffix) is None:
        return None
    module = ".".join((*path.parts[:-1], stem))
    return module if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*", module) else None


def seed_artifacts(source_build: Path, destination_build: Path, allowed: set[str]) -> dict:
    require(not source_build.is_symlink() and not destination_build.is_symlink(),
            "Project build directories must not be symlinks.")
    source_files = regular_files(source_build)
    destination_build.mkdir(parents=True, exist_ok=True)
    # Reject symlinks anywhere in the restored project cache before any copy.
    initial = regular_files(destination_build)
    initial_state = {relative: (sha256(path), path.stat().st_mode & 0o777)
                     for relative, path in initial.items()}
    entries = []
    skipped = []
    copied = reused = 0
    for relative, source in sorted(source_files.items()):
        module = module_for_artifact(relative)
        if module is None or module not in allowed:
            skipped.append({"path": relative, "reason": "OUTSIDE_MATCHING_NATIVE_MODULE_ARTIFACTS"})
            continue
        source_hash = sha256(source)
        target = destination_build / relative
        if target.exists():
            require(target.is_file() and not target.is_symlink(), "Existing project artifact has an invalid type.")
            target_hash = sha256(target)
            disposition = "PRESERVED_EXISTING"
            reused += 1
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            # Exclusive creation preserves a concurrently created cache entry.
            with source.open("rb") as incoming, target.open("xb") as outgoing:
                shutil.copyfileobj(incoming, outgoing, 1024 * 1024)
            shutil.copystat(source, target, follow_symlinks=False)
            target_hash = sha256(target)
            require(target_hash == source_hash == sha256(source), "Project cache seed copy changed bytes.")
            require((target.stat().st_mode & 0o777) == (source.stat().st_mode & 0o777),
                    "Project cache seed copy changed file mode.")
            disposition = "COPIED_MISSING"
            copied += 1
        entries.append({"path": relative, "module": module, "status": disposition,
                        "source_sha256": source_hash, "destination_sha256": target_hash,
                        "source_matches_destination": source_hash == target_hash,
                        "source_mode": oct(source.stat().st_mode & 0o777),
                        "destination_mode": oct(target.stat().st_mode & 0o777),
                        "size_bytes": target.stat().st_size})
    # Files outside the selected artifact set are preserved as well.
    require(all(path.is_file() and not path.is_symlink() and
                (sha256(path), path.stat().st_mode & 0o777) == initial_state[relative]
                for relative, path in initial.items()),
            "An existing project cache file changed during seeding.")
    return {"copied_files": copied, "reused_existing_files": reused, "skipped_files": len(skipped),
            "existing_cache_files_preserved": len(initial),
            "artifacts": entries, "skipped": skipped}


def seed(repo: Path, stage: Path, package: str, report: Path, commit: str) -> dict:
    require(re.fullmatch(r"[a-f0-9]{40}", commit) is not None, "Expected an exact lowercase Git source SHA.")
    require(git(repo, "rev-parse", "HEAD") == commit, "Repository Git HEAD differs from the requested source.")
    require(not stage.is_relative_to(repo) and not repo.is_relative_to(stage),
            "Standalone project cache must be outside the repository.")
    require(not (stage / ".lake").is_symlink() and not (repo / ".lake").is_symlink(),
            "Project Lake directories must not be symlinks.")
    provenance_path = report / "run-provenance.json"
    audit_path = report / "audit-summary.json"
    source_manifest_path = report / "source-manifest.json"
    provenance, audit, source_manifest = (read_json(p) for p in
                                         (provenance_path, audit_path, source_manifest_path))
    require(provenance["source_commit"] == audit["source_commit"] == source_manifest["source_commit"] == commit and
            provenance["build_status"] == "PASS" and provenance["audit_command_status"] == "PASS" and
            provenance["theorem_axiom_audit_status"] == audit["status"] == "PASS_STANDARD_ONLY" and
            audit["source_input_verification"] == "PASS" and not audit["errors"],
            "Matching successful integrated compilation and fresh axiom audit are required.")
    require(provenance["source_manifest_sha256"] == audit["source_manifest_sha256"] == sha256(source_manifest_path),
            "Root compiler source manifest hash mismatch.")
    compiled = {entry["path"]: entry for entry in source_manifest["files"]}
    require(len(compiled) == len(source_manifest["files"]), "Duplicate root compiler source entries.")
    short = PACKAGES[package]
    isolation_path = report / (short + "-isolation-manifest.json")
    isolation = read_json(isolation_path)
    require(isolation["source_commit"] == commit and isolation["isolated_root"] == str(stage) and
            isolation["shared_dependency_source_cache"] is False,
            "Matching independent package preparation is required before project cache seeding.")
    recorded = {entry["isolated_path"]: entry for entry in isolation["files"]}
    require(len(recorded) == len(isolation["files"]), "Duplicate prepared source inventory entries.")
    actual = regular_files(stage, exclude_lake=True)
    require(set(recorded) == set(actual), "Standalone package source inventory changed after preparation.")
    for relative, path in actual.items():
        safe_relative(relative)
        require(sha256(path) == recorded[relative]["sha256"] and
                path.stat().st_size == recorded[relative]["size_bytes"],
                f"Prepared standalone source bytes changed: {relative}")
    modules = module_sources(set(recorded), package)
    canonical_roots = module_roots(package, canonical=True)
    identities = []
    for module, relative in sorted(modules.items()):
        canonical = canonical_roots[module.split(".")[0]] + "/" + module.replace(".", "/") + ".lean"
        require(canonical in compiled, f"Root compiler manifest does not contain module: {module}")
        source = repo / canonical
        require(source.is_file() and not source.is_symlink() and
                sha256(source) == compiled[canonical]["sha256"] == recorded[relative]["sha256"],
                f"Root and standalone module source identities differ: {module}")
        identities.append({"module": module, "canonical_path": canonical, "isolated_path": relative,
                           "sha256": recorded[relative]["sha256"]})
    results = seed_artifacts(repo / ".lake/build", stage / ".lake/build", set(modules))
    return {"schema_version": 1, "status": "PASS", "source_commit": commit, "package_name": package,
            "source_build_root": str(repo / ".lake/build"), "destination_build_root": str(stage / ".lake/build"),
            "root_provenance_sha256": sha256(provenance_path), "root_audit_sha256": sha256(audit_path),
            "root_source_manifest_sha256": sha256(source_manifest_path),
            "isolation_manifest_sha256": sha256(isolation_path),
            "sharing_mode": "PHYSICAL_COPIES_ONLY", "overwrites_existing_files": False,
            "shared_project_object_cache": False, "verified_source_modules": identities,
            "lake_transitive_freshness_check": "REQUIRED_AFTER_SEEDING",
            "fresh_standalone_axiom_audit": "REQUIRED_AFTER_SEEDING", "lean_lake_elan_executions": 0,
            **results}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--package-name", choices=tuple(PACKAGES), required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    args = parser.parse_args()
    report = args.report_directory.resolve()
    try:
        require(not args.destination.is_symlink(), "Standalone destination is linked.")
        result = seed(args.repo_root.resolve(), args.destination.resolve(), args.package_name,
                      report, args.source_commit)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        result = {"schema_version": 1, "status": "FAIL", "source_commit": args.source_commit,
                  "package_name": args.package_name, "error": str(error), "lean_lake_elan_executions": 0}
    report.mkdir(parents=True, exist_ok=True)
    (report / (PACKAGES[args.package_name] + "-project-cache-seed.json")).write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in {"artifacts", "skipped", "verified_source_modules"}}, indent=2))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
