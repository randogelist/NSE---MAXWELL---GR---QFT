#!/usr/bin/env python3
"""Prepare and verify an isolated Maxwell package; never invoke Lean."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path


PREFIX = "Maxwell_Endpoint"
EXPECTED_LEAN = "leanprover/lean4:v4.34.0-rc1"
EXPECTED_MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def git(repo: Path, *arguments: str) -> str:
    return subprocess.run(
        ["git", "-C", str(repo), *arguments], check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    ).stdout


def without_comments(text: str) -> str:
    result: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            if not depth or text[i] == "\n":
                result.append(text[i])
            i += 1
    require(depth == 0, "Unclosed Lean block comment.")
    return "".join(result)


def check_imports(root: Path, paths: set[str]) -> dict[str, list[str]]:
    imports: dict[str, list[str]] = {}
    for relative in sorted(paths):
        if not relative.endswith(".lean") or relative == "lakefile.lean":
            continue
        text = without_comments((root / relative).read_text(encoding="utf-8-sig"))
        names: list[str] = []
        for match in re.finditer(r"^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", text, re.M):
            for name in match.group(1).split():
                require(
                    re.fullmatch(r"(?:Mathlib|MaxwellEndpoint)(?:\.[A-Za-z0-9_]+)*", name) is not None,
                    f"Non-standalone module import in {relative}: {name}",
                )
                if name == "MaxwellEndpoint" or name.startswith("MaxwellEndpoint."):
                    require(name.replace(".", "/") + ".lean" in paths,
                            f"Missing native imported source: {name}")
                names.append(name)
        imports[relative] = names
    return imports


def source_files(repo: Path) -> dict[str, Path]:
    result: dict[str, Path] = {}
    package = repo / PREFIX
    require(not package.is_symlink(), "Package source root must not be a symlink.")
    for raw in git(repo, "ls-files", "-z", "--", PREFIX).split("\0"):
        if not raw:
            continue
        path = Path(raw)
        require(path.parts[0] == PREFIX and ".." not in path.parts,
                f"Invalid tracked package path: {raw}")
        relative = Path(*path.parts[1:])
        require(relative.parts and relative.parts[0] not in {
            ".lake", ".git", "artifacts", ".mathlib-download-cache",
        }, f"Generated path tracked as package source: {raw}")
        current = repo
        for part in path.parts:
            current = current / part
            require(not current.is_symlink(), f"Symbolic link in package source: {raw}")
        require(current.is_file(), f"Missing tracked package source: {raw}")
        result[relative.as_posix()] = current
    for required in ("MaxwellEndpoint.lean", "MaxwellEndpoint/Audit.lean", "lakefile.lean",
                     "lean-toolchain", "lake-manifest.json", "audit-targets.txt", "run.sh",
                     "run.cmd", "scripts/run.ps1", "scripts/verify_audit.py"):
        require(required in result, f"Missing standalone package file: {required}")
    require((package / "lean-toolchain").read_text().strip() == EXPECTED_LEAN,
            "Standalone compiler pin mismatch.")
    lock = read_json(package / "lake-manifest.json")
    require(lock["packages"] == read_json(repo / "lake-manifest.json")["packages"],
            "Standalone and root dependency locks differ.")
    require(lock["packagesDir"] == ".lake/packages", "Unexpected standalone package directory.")
    mathlib = [p for p in lock["packages"] if p["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == EXPECTED_MATHLIB,
            "Standalone Mathlib pin mismatch.")
    return result


def check_isolation(stage: Path, packages: Path, expected_paths: set[str]) -> None:
    require(not (stage / ".lake").is_symlink(), "Standalone Lake directory is linked.")
    link = stage / ".lake/packages"
    require(link.is_symlink() and link.resolve() == packages,
            "Standalone dependency link does not target the verified cache.")
    require(not (stage / ".lake/build").is_symlink(), "Standalone project build directory is linked.")
    observed: set[str] = set()
    for directory, subdirs, names in os.walk(stage, followlinks=False):
        base = Path(directory)
        if base == stage:
            subdirs[:] = [name for name in subdirs if name != ".lake"]
        for name in subdirs + names:
            require(not (base / name).is_symlink(), "Symbolic link in isolated package sources.")
        observed.update((base / name).relative_to(stage).as_posix() for name in names)
    require(observed == expected_paths, "Isolated package source inventory changed.")
    native = stage / ".lake/build/lib/lean"
    if native.exists():
        for path in native.rglob("*"):
            require(not path.is_symlink(), "Linked standalone compiled object.")
            first = path.relative_to(native).parts[0]
            require(first == "MaxwellEndpoint" or first.startswith("MaxwellEndpoint."),
                    f"Unexpected non-Maxwell project object: {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("prepare", "verify"))
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    args = parser.parse_args()
    repo, stage, report = (args.repo_root.resolve(), args.destination.resolve(),
                           args.report_directory.resolve())
    result_path = report / "maxwell-isolation-result.json"
    try:
        require(re.fullmatch(r"[a-f0-9]{40}", args.source_commit) is not None,
                "Expected a lowercase 40-hex source commit.")
        require(git(repo, "rev-parse", "HEAD").strip() == args.source_commit, "Git HEAD mismatch.")
        require(not stage.is_relative_to(repo), "Standalone directory must be outside the repository.")
        require(not repo.is_relative_to(stage), "Standalone directory must not contain the repository.")
        require(not args.destination.is_symlink(), "Standalone destination must not be a symlink.")
        root_provenance = read_json(report / "run-provenance.json")
        require(root_provenance["source_commit"] == args.source_commit and
                root_provenance["build_status"] == "PASS" and
                root_provenance["theorem_axiom_audit_status"] == "PASS_STANDARD_ONLY",
                "Matching successful integrated build/audit is required.")
        files = source_files(repo)
        imports = check_imports(repo / PREFIX, set(files))
        packages = (repo / ".lake/packages").resolve()
        require(packages.is_dir(), "Verified dependency cache is absent.")
        manifest_path = report / "maxwell-isolation-manifest.json"
        if args.phase == "prepare":
            stage.mkdir(parents=True, exist_ok=True)
            require(all(p.name == ".lake" for p in stage.iterdir()),
                    "Destination already contains non-cache files; no files will be removed.")
            (stage / ".lake").mkdir(exist_ok=True)
            require(not (stage / ".lake").is_symlink(), "Linked standalone Lake directory.")
            link = stage / ".lake/packages"
            if not link.exists() and not link.is_symlink():
                link.symlink_to(packages, target_is_directory=True)
            entries = []
            for relative, source in sorted(files.items()):
                target = stage / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(source.read_bytes())
                require(sha256(source) == sha256(target), f"Copy hash mismatch: {relative}")
                entries.append({"source_path": PREFIX + "/" + relative,
                                "isolated_path": relative, "sha256": sha256(source),
                                "size_bytes": source.stat().st_size})
            check_isolation(stage, packages, set(files))
            write_json(manifest_path, {"schema_version": 1, "source_commit": args.source_commit,
                       "isolated_root": str(stage), "dependency_cache": str(packages),
                       "files": entries, "imports": imports, "status": "PREPARED"})
            write_json(result_path, {"status": "PREPARED", "source_commit": args.source_commit,
                                    "copied_files": len(entries), "standalone_audit": "PENDING"})
        else:
            manifest = read_json(manifest_path)
            require(manifest["source_commit"] == args.source_commit and
                    manifest["isolated_root"] == str(stage) and
                    manifest["dependency_cache"] == str(packages), "Isolation provenance mismatch.")
            recorded = {item["isolated_path"]: item for item in manifest["files"]}
            require(set(recorded) == set(files), "Tracked package inventory changed.")
            check_isolation(stage, packages, set(files))
            require(check_imports(stage, set(files)) == imports == manifest["imports"],
                    "Native import graph changed.")
            for relative, source in files.items():
                require(sha256(source) == sha256(stage / relative) == recorded[relative]["sha256"],
                        f"Source bytes changed during standalone validation: {relative}")
            evidence = report / "standalone"
            provenance, audit = read_json(evidence / "run-provenance.json"), read_json(evidence / "audit-summary.json")
            compiled = read_json(evidence / "source-manifest.json")
            require(provenance["source_commit"] == audit["source_commit"] ==
                    compiled["source_commit"] == args.source_commit, "Standalone commit mismatch.")
            require(Path(provenance["package_root"]).resolve() == stage,
                    "Standalone compiler used a different package root.")
            require(provenance["external_platform"] == "linux" and
                    provenance["requested_toolchain"] == EXPECTED_LEAN and
                    provenance["actual_mathlib_commit"] == EXPECTED_MATHLIB and
                    provenance["build_status"] == "PASS" and
                    provenance["audit_command_status"] == "PASS" and
                    provenance["theorem_axiom_audit_status"] == "PASS_STANDARD_ONLY" and
                    audit["status"] == "PASS_STANDARD_ONLY" and
                    audit["source_input_verification"] == "PASS" and not audit["errors"],
                    "Standalone compiler/audit evidence did not pass.")
            targets = [line.strip() for line in (stage / "audit-targets.txt").read_text().splitlines()
                       if line.strip() and not line.lstrip().startswith("#")]
            require(targets and len(targets) == len(set(targets)) and
                    [item["name"] for item in audit["theorems"]] == targets,
                    "Standalone audit differs from the exact declared target inventory.")
            require(all(item["status"] == "PASS_STANDARD_ONLY" and
                        set(item["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
                        for item in audit["theorems"]), "Invalid standalone theorem axiom record.")
            require(sha256(evidence / "source-manifest.json") ==
                    provenance["source_manifest_sha256"] == audit["source_manifest_sha256"],
                    "Standalone compiler manifest hash mismatch.")
            compiled_files = {item["path"]: item["sha256"] for item in compiled["files"]}
            require(compiled_files == {name: item["sha256"] for name, item in recorded.items()},
                    "Standalone compiler did not verify the exact isolated source inventory.")
            write_json(result_path, {"schema_version": 1, "status": "PASS",
                       "source_commit": args.source_commit, "source_files_verified": len(files),
                       "standalone_audited_declarations": len(audit["theorems"]),
                       "isolation_manifest_sha256": sha256(manifest_path),
                       "standalone_source_manifest_sha256": sha256(evidence / "source-manifest.json"),
                       "standalone_audit": "PASS_STANDARD_ONLY",
                       "shared_dependency_cache": True, "shared_project_object_cache": False,
                       "semantic_discharge": "NOT_INFERRED_FROM_PACKAGE_COMPILATION"})
        print(f"MAXWELL_ISOLATION={args.phase.upper()}_PASS")
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        write_json(result_path, {"status": "FAIL", "phase": args.phase, "error": str(error),
                                "source_commit": args.source_commit})
        print(f"MAXWELL_ISOLATION=FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
