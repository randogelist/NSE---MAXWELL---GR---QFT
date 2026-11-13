#!/usr/bin/env python3
"""Prepare and verify isolated native adapters; never invoke Lean."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path


PACKAGES = {"Maxwell_Endpoint": "maxwell", "Fefferman_adapter": "fefferman"}
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


def copy_source(source: Path, target: Path) -> None:
    target.write_bytes(source.read_bytes())
    if os.name == "posix":
        target.chmod(source.stat().st_mode & 0o777)


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


def project_modules(paths: set[str], package: str) -> dict[str, str]:
    roots = {"MethlibEndpoints": "", "SingularClosure": "NativeSources/methlib"}
    if package == "Maxwell_Endpoint":
        roots["MaxwellEndpoint"] = ""
    else:
        roots.update({"NSEMaxwell": "", "FourierHodgeLaws": "",
                      "FourierHodgeLaws_inhabitant": "", "MaxwellEndpoint": "LocalDependencies/Maxwell",
                      "NSEMaxwellForward": "LocalDependencies/Forward",
                      "NSEMaxwellReverse": "LocalDependencies/Reverse"})
    modules: dict[str, str] = {}
    for namespace, prefix in roots.items():
        stem = (prefix + "/" if prefix else "") + namespace
        for relative in sorted(paths):
            if (relative == stem + ".lean" or
                    relative.startswith(stem + "/") and relative.endswith(".lean")):
                suffix = relative[len(prefix) + 1:] if prefix else relative
                name = suffix[:-5].replace("/", ".")
                require(name not in modules, f"Duplicate project module: {name}")
                modules[name] = relative
    require(modules, "No active native implementation sources found.")
    return modules


def check_imports(root: Path, paths: set[str], package: str) -> dict[str, list[str]]:
    modules = project_modules(paths, package)
    imports: dict[str, list[str]] = {}
    for module, relative in sorted(modules.items()):
        text = without_comments((root / relative).read_text(encoding="utf-8-sig"))
        names: list[str] = []
        for match in re.finditer(r"^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", text, re.M):
            for name in match.group(1).split():
                require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*", name)
                        is not None, f"Invalid module import in {relative}: {name}")
                require(name in modules or name == "Mathlib" or name.startswith("Mathlib."),
                        f"Missing native imported source in {relative}: {name}")
                names.append(name)
        imports[relative] = names
    return imports


def check_local_copies(repo: Path, package: str, files: dict[str, Path]) -> None:
    if package != "Fefferman_adapter":
        return
    inventory = read_json(repo / package / "local-project-sources.json")
    require(isinstance(inventory.get("files"), list) and inventory["files"],
            "Fefferman local project source inventory is absent.")
    recorded: set[str] = set()
    for entry in inventory["files"]:
        source, target = entry["source_path"], entry["package_path"]
        require(not Path(source).is_absolute() and ".." not in Path(source).parts,
                "Invalid canonical project source path.")
        require(target in files and target not in recorded and
                target.startswith("LocalDependencies/"), "Invalid local project copy record.")
        recorded.add(target)
        original = repo / source
        require(original.is_file() and not original.is_symlink(), "Missing canonical project source.")
        require(sha256(original) == sha256(files[target]) == entry["sha256"] and
                original.stat().st_size == files[target].stat().st_size == entry["size_bytes"],
                f"Canonical project copy differs: {target}")
    expected = {path for path in files if path.startswith("LocalDependencies/") and path.endswith(".lean")}
    require(recorded == expected, "Local project copy inventory is incomplete.")


def source_files(repo: Path, prefix: str) -> dict[str, Path]:
    result: dict[str, Path] = {}
    package = repo / prefix
    require(not package.is_symlink(), "Package source root must not be a symlink.")
    for raw in git(repo, "ls-files", "-z", "--", prefix).split("\0"):
        if not raw:
            continue
        path = Path(raw)
        require(path.parts[0] == prefix and ".." not in path.parts,
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
    required = {"lakefile.lean", "lean-toolchain", "lake-manifest.json", "audit-targets.txt",
                "cache-targets.txt", "run.sh", "run.cmd", "scripts/run.ps1",
                "scripts/verify_audit.py", "scripts/verify_native_sources.py", "scripts/hydrate_native_sources.py", "native-sources.json",
                "MethlibEndpoints.lean", "MethlibEndpoints/Audit.lean", "methlib-module-order.json",
                "methlib-audit-targets.txt", "NativeSources/methlib/SOURCE_MANIFEST.json"}
    if prefix == "Maxwell_Endpoint":
        required.update({"MaxwellEndpoint.lean", "MaxwellEndpoint/Audit.lean"})
    else:
        required.update({"NSEMaxwell.lean", "NSEMaxwell/Audit.lean", "local-project-sources.json",
                         "FourierHodgeLaws_inhabitant.lean", "FourierHodgeLaws/Inhabitant.lean"})
    for relative in required:
        require(relative in result, f"Missing standalone package file: {relative}")
    check_local_copies(repo, prefix, result)
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


def check_isolation(stage: Path, packages: Path, expected_paths: set[str], package: str) -> None:
    require(not (stage / ".lake").is_symlink(), "Standalone Lake directory is linked.")
    source_root = stage / ".lake/packages"
    require(source_root.is_dir() and not source_root.is_symlink(),
            "Standalone dependency source root must be an independent directory.")
    pins = read_json(stage / "lake-manifest.json")["packages"]
    require({item.name for item in source_root.iterdir()} == {pin["name"] for pin in pins},
            "Standalone dependency source inventory differs from the pinned packages.")
    for pin in pins:
        dependency = source_root / pin["name"]
        require(dependency.is_dir() and not dependency.is_symlink() and
                (dependency / ".git").is_dir() and not (dependency / ".git").is_symlink(),
                "Standalone dependency source checkout is shared or absent.")
        require(git(dependency, "rev-parse", "HEAD").strip() == pin["rev"],
                "Standalone native dependency revision mismatch.")
        require(not git(dependency, "status", "--porcelain", "--untracked-files=no").strip(),
                "Standalone native dependency worktree changed.")
        compiled = packages / pin["name"] / ".lake/build"
        link = dependency / ".lake/build"
        if compiled.is_dir():
            require(link.is_symlink() and link.resolve() == compiled.resolve(),
                    "Standalone compiled dependency link differs from the verified cache.")
        else:
            require(not link.is_symlink(), "Unexpected standalone dependency build symlink.")
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
    namespaces = {name.split(".")[0] for name in project_modules(expected_paths, package)}
    if native.exists():
        for path in native.rglob("*"):
            require(not path.is_symlink(), "Linked standalone compiled object.")
            first = path.relative_to(native).parts[0]
            require(any(first == name or first.startswith(name + ".") for name in namespaces),
                    f"Unexpected project object namespace: {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("prepare", "verify"))
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--package-name", choices=tuple(PACKAGES), default="Maxwell_Endpoint")
    args = parser.parse_args()
    repo, stage, report = (args.repo_root.resolve(), args.destination.resolve(),
                           args.report_directory.resolve())
    prefix = args.package_name
    short_name = PACKAGES[prefix]
    evidence_name = "standalone" if prefix == "Maxwell_Endpoint" else "fefferman-standalone"
    result_path = report / (short_name + "-isolation-result.json")
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
        files = source_files(repo, prefix)
        imports = check_imports(repo / prefix, set(files), prefix)
        packages = (repo / ".lake/packages").resolve()
        require(packages.is_dir(), "Verified dependency cache is absent.")
        manifest_path = report / (short_name + "-isolation-manifest.json")
        if args.phase == "prepare":
            stage.mkdir(parents=True, exist_ok=True)
            require(all(p.name == ".lake" for p in stage.iterdir()),
                    "Destination already contains non-cache files; no files will be removed.")
            (stage / ".lake").mkdir(exist_ok=True)
            require(not (stage / ".lake").is_symlink(), "Linked standalone Lake directory.")
            entries = []
            for relative, source in sorted(files.items()):
                target = stage / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                copy_source(source, target)
                require(sha256(source) == sha256(target), f"Copy hash mismatch: {relative}")
                entries.append({"source_path": prefix + "/" + relative,
                                "isolated_path": relative, "sha256": sha256(source),
                                "size_bytes": source.stat().st_size,
                                "mode_octal": format(source.stat().st_mode & 0o777, "04o")
                                if os.name == "posix" else None})
            hydration_path = report / (short_name + "-source-hydration.json")
            subprocess.run([
                sys.executable, str(stage / "scripts/hydrate_native_sources.py"),
                "--package-root", str(stage),
                "--dependency-root", str(stage / ".lake/packages"),
                "--compiled-cache-root", str(packages),
                "--report", str(hydration_path),
            ], check=True)
            hydration = read_json(hydration_path)
            require(hydration.get("status") == "PASS" and hydration.get("dependency_count") == 9 and
                    hydration.get("dependency_source_downloads") == 0 and
                    hydration.get("shared_source_checkouts") is False and
                    all(item["status"] == "RESTORED_FROM_CONTAINED_NATIVE_SOURCES"
                        for item in hydration["dependencies"]),
                    "Standalone dependencies were not reconstructed from contained native source bytes.")
            check_isolation(stage, packages, set(files), prefix)
            write_json(manifest_path, {"schema_version": 2, "source_commit": args.source_commit,
                       "isolated_root": str(stage), "compiled_dependency_cache": str(packages),
                       "dependency_source_root": str(stage / ".lake/packages"),
                       "source_hydration_report": hydration_path.name,
                       "source_hydration_sha256": sha256(hydration_path),
                       "shared_dependency_source_cache": False,
                       "files": entries, "imports": imports, "status": "PREPARED"})
            write_json(result_path, {"status": "PREPARED", "source_commit": args.source_commit,
                                    "copied_files": len(entries), "standalone_audit": "PENDING"})
        else:
            manifest = read_json(manifest_path)
            require(manifest["source_commit"] == args.source_commit and
                    manifest["isolated_root"] == str(stage) and
                    manifest["compiled_dependency_cache"] == str(packages) and
                    manifest["dependency_source_root"] == str(stage / ".lake/packages") and
                    manifest["shared_dependency_source_cache"] is False,
                    "Isolation provenance mismatch.")
            hydration_path = report / (short_name + "-source-hydration.json")
            require(manifest["source_hydration_report"] == hydration_path.name and
                    manifest["source_hydration_sha256"] == sha256(hydration_path),
                    "Standalone source hydration provenance changed.")
            hydration = read_json(hydration_path)
            require(hydration.get("status") == "PASS" and hydration.get("dependency_source_downloads") == 0 and
                    hydration.get("dependency_count") == 9 and hydration.get("shared_source_checkouts") is False,
                    "Standalone contained source hydration did not pass.")
            recorded = {item["isolated_path"]: item for item in manifest["files"]}
            require(set(recorded) == set(files), "Tracked package inventory changed.")
            check_isolation(stage, packages, set(files), prefix)
            require(check_imports(stage, set(files), prefix) == imports == manifest["imports"],
                    "Native import graph changed.")
            for relative, source in files.items():
                require(sha256(source) == sha256(stage / relative) == recorded[relative]["sha256"],
                        f"Source bytes changed during standalone validation: {relative}")
                if os.name == "posix":
                    source_mode = source.stat().st_mode & 0o777
                    require((stage / relative).stat().st_mode & 0o777 == source_mode and
                            recorded[relative].get("mode_octal") == format(source_mode, "04o"),
                            f"Source mode changed during standalone validation: {relative}")
            evidence = report / evidence_name
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
            native_report = evidence / "native-source-closure.json"
            native = read_json(native_report)
            require(native.get("status") == "PASS", "Standalone native source closure failed.")
            records = provenance.get("native_source_closure")
            require(isinstance(records, list) and len(records) == 1 and
                    records[0].get("report") == native_report.name and
                    records[0].get("sha256") == sha256(native_report),
                    "Standalone native source closure provenance mismatch.")
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
            seed_record = None
            seed_path = report / (short_name + "-project-cache-seed.json")
            if seed_path.exists():
                seed = read_json(seed_path)
                require(seed.get("status") == "PASS" and
                        seed.get("source_commit") == args.source_commit and
                        seed.get("package_name") == prefix and
                        seed.get("sharing_mode") == "PHYSICAL_COPIES_ONLY" and
                        seed.get("overwrites_existing_files") is False and
                        seed.get("shared_project_object_cache") is False and
                        seed.get("isolation_manifest_sha256") == sha256(manifest_path),
                        "Standalone project cache seed provenance mismatch.")
                seed_record = {"report": seed_path.name, "sha256": sha256(seed_path),
                               "copied_files": seed["copied_files"],
                               "reused_existing_files": seed["reused_existing_files"],
                               "sharing_mode": "PHYSICAL_COPIES_ONLY"}
            write_json(result_path, {"schema_version": 1, "status": "PASS",
                       "source_commit": args.source_commit, "source_files_verified": len(files),
                       "standalone_audited_declarations": len(audit["theorems"]),
                       "isolation_manifest_sha256": sha256(manifest_path),
                       "standalone_source_manifest_sha256": sha256(evidence / "source-manifest.json"),
                       "standalone_audit": "PASS_STANDARD_ONLY",
                       "shared_dependency_cache": "COMPILED_OBJECTS_ONLY",
                       "project_cache_seed": seed_record,
                       "shared_dependency_source_cache": False, "shared_project_object_cache": False,
                       "source_hydration_sha256": sha256(hydration_path),
                       "dependency_source_downloads": 0,
                       "package_name": prefix, "native_source_closure": "PASS",
                       "semantic_discharge": "NOT_INFERRED_FROM_PACKAGE_COMPILATION"})
        print(f"{short_name.upper()}_ISOLATION={args.phase.upper()}_PASS")
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        write_json(result_path, {"status": "FAIL", "phase": args.phase, "error": str(error),
                                "source_commit": args.source_commit})
        print(f"{short_name.upper()}_ISOLATION=FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
