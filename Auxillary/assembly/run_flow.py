#!/usr/bin/env python3
"""Audit native Flow modules independently on the external cached Lean compiler.

Each module receives its own build, fresh named theorem audit, and source manifest.
A failed module does not suppress unrelated modules. The final exit code remains
nonzero for a partial failure; individual passing certificates remain available.
This runner never promotes the exact L1 endpoint automatically.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


REGISTRY = "Auxillary/assembly/flow-targets.json"
SCOPE = "Auxillary/assembly/flow-status.json"
FLOW_PREFIX = "ClassicalMechanicsAssembly.Flow"
FOUNDATIONS = frozenset({"propext", "Classical.choice", "Quot.sound"})
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8-sig"))
    require(isinstance(value, dict), f"JSON object required: {path}")
    return value


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def helper(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f"Cannot load helper: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def registry_modules(registry: dict) -> list[dict]:
    require(registry.get("schema_version") == 1 and registry.get("audit_policy") == "FOUNDATIONAL_ONLY",
            "A foundational-only native flow registry is required.")
    modules = registry.get("modules", [])
    require(isinstance(modules, list) and modules, "At least one registered Flow module is required.")
    seen_modules: set[str] = set()
    seen_targets: set[str] = set()
    for entry in modules:
        module, names = entry.get("module"), entry.get("targets")
        require(isinstance(module, str) and re.fullmatch(r"ClassicalMechanicsAssembly\.Flow[A-Za-z0-9_]+", module) is not None,
                f"Invalid native Flow module: {module}")
        require(module not in seen_modules, f"Duplicate module: {module}")
        require(isinstance(names, list) and names and all(isinstance(n, str) and
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", n) for n in names), f"Invalid theorem list: {module}")
        require(len(names) == len(set(names)) and not seen_targets.intersection(names),
                f"Duplicate registered audit targets: {module}")
        seen_modules.add(module)
        seen_targets.update(names)
    return modules


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external-native-linux", action="store_true", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--standard-report-directory", type=Path, required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    args = parser.parse_args()
    root, standard, report = args.repo_root.resolve(), args.standard_report_directory.resolve(), args.report_directory.resolve()
    require(report.is_relative_to(root) and report != root and report != standard, "Distinct report directory below root required.")
    report.mkdir(parents=True, exist_ok=True)
    aggregate: dict = {"schema_version": 1, "status": "INITIALIZE", "modules": [],
        "local_lean_executions": 0, "allowed_axioms": sorted(FOUNDATIONS),
        "L1_status": "NOT_PROMOTED_BY_PARTIAL_MODULE_AUDITS",
        "literature_L1": "NATIVE_COMPATIBILITY_THEOREM; CURRENT_AUDIT_REQUIRED"}

    def save() -> None:
        write_json(report / "aggregate-summary.json", aggregate)

    def run(command: list[str], path: Path) -> subprocess.CompletedProcess:
        env = os.environ.copy()
        env["ELAN_TOOLCHAIN"] = TOOLCHAIN
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
        env.pop("LEAN_PATH", None)
        env.pop("LEAN_SRC_PATH", None)
        start = time.monotonic()
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w", encoding="utf-8", newline="\n") as stream:
            process = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace", bufsize=1)
            lines = []
            assert process.stdout is not None
            for line in process.stdout:
                lines.append(line)
                stream.write(line)
                stream.flush()
                print(line, end="", flush=True)
            code = process.wait()
        write_json(path.with_suffix(path.suffix + ".command.json"), {"command": command,
            "exit_code": code, "elapsed_seconds": round(time.monotonic() - start, 3)})
        return subprocess.CompletedProcess(command, code, "".join(lines))

    try:
        require(args.external_native_linux and sys.platform.startswith("linux"), "Explicit external native Linux required.")
        assembly = helper(root / "Auxillary/assembly/run.py", "flow_assembly_helper")
        axiom_parser = helper(root / "Auxillary/scripts/verify_audit.py", "flow_axiom_parser")
        require(axiom_parser.ALLOWED_AXIOMS == FOUNDATIONS, "Shared foundational-only allowlist changed.")
        parent = read_json(standard / "run-provenance.json")
        prior_audit = read_json(standard / "audit-summary.json")
        parent_manifest = read_json(standard / "source-manifest.json")
        require(parent.get("build_status") == parent.get("audit_command_status") == "PASS"
                and parent.get("theorem_axiom_audit_status") == prior_audit.get("status") == "PASS_STANDARD_ONLY",
                "The preserved standard-only assembly audit must pass first.")
        require(parent.get("audit_target_count") == 43 and len(prior_audit.get("theorems", [])) == 43,
                "The preserved 43-target audit is required.")
        require(parent.get("external_native_linux") is True and parent.get("requested_toolchain") == TOOLCHAIN
                and parent.get("actual_mathlib_commit") == MATHLIB and parent.get("dependency_cache_status") == "VERIFIED",
                "Matching external pinned cached dependencies are required.")
        require(digest(standard / "source-manifest.json") == parent.get("source_manifest_sha256") == prior_audit.get("source_manifest_sha256"),
                "Parent source-manifest hash mismatch.")
        commit = run(["git", "rev-parse", "HEAD"], report / "source-commit.log")
        require(commit.returncode == 0 and commit.stdout.strip() == parent.get("source_commit")
                and (not os.environ.get("GITHUB_SHA") or commit.stdout.strip() == os.environ["GITHUB_SHA"]), "Source commit mismatch.")
        status = run(["git", "status", "--porcelain", "--untracked-files=no"], report / "working-tree.log")
        require(status.returncode == 0 and not status.stdout.strip(), "Tracked source modifications after standard audit.")
        version = run(["lean", "--version"], report / "lean-version.log")
        require(version.returncode == 0 and version.stdout.strip() == parent.get("actual_lean_version"), "Compiler version changed.")
        require(digest(root / "lake-manifest.json") == parent.get("lockfile_sha256"), "Dependency lock changed.")
        files = {item["path"]: item for item in parent_manifest["files"]}
        require(len(files) == len(parent_manifest["files"]), "Duplicate source manifest paths.")
        for relative, item in files.items():
            path = (root / relative).resolve()
            require(path.is_relative_to(root) and path.is_file() and not path.is_symlink()
                    and digest(path) == item["sha256"], f"Source input changed: {relative}")
        required_infrastructure = {REGISTRY, SCOPE, "Auxillary/assembly/run_flow.py", "Auxillary/run_flow.sh"}
        require(required_infrastructure.issubset(files), "Untracked flow registry/runner/status.")
        registry = read_json(root / REGISTRY)
        modules = registry_modules(registry)
        by_name = {item["module"]: item for item in modules}
        discovered = {"ClassicalMechanicsAssembly." + Path(path).stem for path in files
                      if re.fullmatch(r"ASSEMBLY/ClassicalMechanicsAssembly/Flow[^/]*\.lean", path)}
        require(discovered == set(by_name), "Every actual Flow*.lean source must have an exact audit registry entry.")
        closures = {}
        dependencies = {}
        for module in by_name:
            previous_root = assembly.ROOT_MODULE
            try:
                assembly.ROOT_MODULE = module
                closure, external = assembly.local_closure(root)
            finally:
                assembly.ROOT_MODULE = previous_root
            require({item["path"] for item in closure}.issubset(files), f"Untracked import closure: {module}")
            closures[module] = {"local_modules": closure, "external_imports": external}
            dependencies[module] = {item["module"] for item in closure
                                    if item["module"].startswith(FLOW_PREFIX) and item["module"] != module}
            require(dependencies[module].issubset(by_name), f"Unregistered Flow dependency: {module}")
        remaining, schedule = list(by_name), []
        while remaining:
            ready = [module for module in remaining if dependencies[module].issubset(schedule)]
            require(ready, "Cyclic native Flow dependency graph.")
            schedule.extend(ready)
            remaining = [module for module in remaining if module not in ready]
        aggregate.update({"status": "RUNNING", "source_commit": parent["source_commit"],
            "actual_lean_version": parent["actual_lean_version"], "mathlib_commit": MATHLIB,
            "registry_sha256": digest(root / REGISTRY), "standard_43_audit_summary_sha256": digest(standard / "audit-summary.json"),
            "standard_43_provenance_sha256": digest(standard / "run-provenance.json"),
            "standard_43_source_manifest_sha256": digest(standard / "source-manifest.json"),
            "module_schedule": schedule, "module_execution": "INDEPENDENT_FAIL_CONTINUING_WITH_DEPENDENCY_BLOCKING"})
        save()
        # Ordinary official cache get preserves existing objects and fetches only
        # missing entries from the new Mathlib import closures.
        cache_targets = sorted({name for closure in closures.values()
                                for name in closure["external_imports"]
                                if name == "Mathlib" or name.startswith("Mathlib.")})
        require(cache_targets, "No Mathlib cache targets in native Flow closures.")
        cached = run(["lake", "exe", "cache", "get", "--cache-from=master,legacy", *cache_targets],
                     report / "incremental-mathlib-cache.log")
        aggregate["incremental_cache"] = {"strategy": "OFFICIAL_INCREMENTAL_CACHE_GET",
            "targets": cache_targets, "exit_code": cached.returncode}
        require(cached.returncode == 0, "Incremental Mathlib cache request failed.")
        for target in cache_targets:
            require((root / ".lake/packages/mathlib/.lake/build/lib/lean" /
                    (target.replace(".", "/") + ".olean")).is_file(), f"Missing cached import: {target}")
        require(digest(root / "lake-manifest.json") == parent["lockfile_sha256"], "Cache request changed dependency lock.")
        save()
        passed: set[str] = set()
        for module in schedule:
            entry = by_name[module]
            module_report = report / module.rsplit(".", 1)[1]
            module_report.mkdir(parents=True, exist_ok=True)
            blocked = sorted(dependencies[module] - passed)
            result = {"module": module, "targets": entry["targets"], "status": "INITIALIZE",
                "build_status": "NOT_RUN", "audit_status": "NOT_RUN", "blocked_by": blocked,
                "report_directory": module_report.relative_to(root).as_posix()}
            aggregate["modules"].append(result)
            if blocked:
                result["status"] = "BLOCKED_BY_FAILED_DEPENDENCY"
                write_json(module_report / "module-summary.json", result)
                save()
                continue
            provenance = dict(parent)
            provenance.update({"phase": "NATIVE_FLOW_MODULE_BUILD_AUDIT", "stage": "BUILD", "module": module,
                "build_status": "NOT_RUN", "audit_command_status": "NOT_RUN", "theorem_axiom_audit_status": "NOT_RUN",
                "audit_target_count": len(entry["targets"]), "source_commit": parent["source_commit"],
                "local_lean_executions": 0, "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
                "flow_registry_sha256": digest(root / REGISTRY)})
            provenance.pop("completed_at_utc", None)
            native_reports = [parent["native_source_hydration"], *parent["native_source_closure"]]
            for record in native_reports:
                name = record["report"]
                require(Path(name).name == name and digest(standard / name) == record["sha256"]
                        and read_json(standard / name).get("status") == "PASS", "Native dependency evidence changed.")
                shutil.copyfile(standard / name, module_report / name)
            audit = module_report / "Audit.lean"
            audit.write_text(f"import {module}\n\nset_option pp.universes true\n\n" +
                "\n".join(f"#check @{name}\n#print axioms {name}" for name in entry["targets"]) + "\n", encoding="utf-8")
            target_file = module_report / "audit-targets.txt"
            target_file.write_text("\n".join(entry["targets"]) + "\n", encoding="utf-8")
            closure_file = module_report / "import-closure.json"
            write_json(closure_file, closures[module])
            inputs = list(files.values()) + [{"path": p.relative_to(root).as_posix(), "sha256": digest(p),
                "size_bytes": p.stat().st_size} for p in (audit, target_file, closure_file)]
            manifest = module_report / "source-manifest.json"
            write_json(manifest, {"schema_version": 1, "source_commit": parent["source_commit"],
                "scope": "unchanged tracked source inputs plus isolated exact module audit",
                "files": sorted(inputs, key=lambda item: item["path"])})
            provenance["source_manifest_sha256"] = digest(manifest)
            provenance["generated_audit_sha256"] = digest(audit)
            provenance["import_closure_sha256"] = digest(closure_file)
            provenance_path = module_report / "run-provenance.json"
            write_json(provenance_path, provenance)
            fresh = run(["lake", "build", "--no-build", module], module_report / "build-freshness.log")
            provenance["freshness_check_exit_code"] = fresh.returncode
            if fresh.returncode == 0:
                build = fresh
                provenance["build_strategy"] = "LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE"
            elif fresh.returncode == 3:
                provenance["build_strategy"] = "INDEPENDENT_INCREMENTAL_MODULE_BUILD"
                build = run(["lake", "build", module], module_report / "build.log")
            else:
                build = fresh
            if build.returncode != 0:
                result.update({"status": "BUILD_FAILED", "build_status": "FAIL", "build_exit_code": build.returncode})
            else:
                result["build_status"] = provenance["build_status"] = "PASS"
                audited = run(["lake", "env", "lean", "-R", str(module_report), str(audit)], module_report / "audit.log")
                if audited.returncode != 0:
                    result.update({"status": "AUDIT_COMMAND_FAILED", "audit_status": "FAIL", "audit_exit_code": audited.returncode})
                else:
                    provenance["audit_command_status"] = "PASS"
                    write_json(provenance_path, provenance)
                    verified = run([sys.executable, "Auxillary/scripts/verify_audit.py", "--expected-platform", "linux",
                        "--root", str(root), "--targets", str(target_file), "--audit-source", str(audit),
                        "--log", str(module_report / "audit.log"), "--manifest", str(manifest),
                        "--provenance", str(provenance_path), "--scope", SCOPE,
                        "--output", str(module_report / "audit-summary.json")], module_report / "audit-verifier.log")
                    if verified.returncode != 0:
                        result.update({"status": "AXIOM_OR_SOURCE_AUDIT_FAILED", "audit_status": "FAIL"})
                    else:
                        passed.add(module)
                        result.update({"status": "PASS_STANDARD_ONLY", "audit_status": "PASS_STANDARD_ONLY",
                            "audit_summary_sha256": digest(module_report / "audit-summary.json"),
                            "source_manifest_sha256": digest(manifest)})
                        provenance["theorem_axiom_audit_status"] = "PASS_STANDARD_ONLY"
            provenance["stage"] = result["status"]
            provenance["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
            write_json(provenance_path, provenance)
            write_json(module_report / "module-summary.json", result)
            save()
            print(f"NATIVE_FLOW_MODULE={module}; STATUS={result['status']}", flush=True)
        aggregate["passed_modules"] = len(passed)
        aggregate["registered_modules"] = len(schedule)
        aggregate["status"] = "PASS_STANDARD_ONLY" if len(passed) == len(schedule) else "PARTIAL_PASS" if passed else "FAIL"
        aggregate["audited_passed_theorems"] = sum(len(item["targets"]) for item in aggregate["modules"] if item["status"] == "PASS_STANDARD_ONLY")
        aggregate["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        save()
        print(f"NATIVE_FLOW_AGGREGATE={aggregate['status']}; PASSED_MODULES={len(passed)}/{len(schedule)}")
        print("EXACT_L1_PROMOTION=REQUIRES_COMPLETE_NATIVE_ROOT_AND_SCOPE_REVIEW")
        return 0 if len(passed) == len(schedule) else 1
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        aggregate["status"] = "INFRASTRUCTURE_FAILED"
        aggregate["failure"] = str(error)
        save()
        print(f"NATIVE_FLOW_INFRASTRUCTURE=FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
