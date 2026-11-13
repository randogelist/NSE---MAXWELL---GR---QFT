#!/usr/bin/env python3
"""Compile and audit only the assembly on an external cached native Linux host.

The existing Dependencies phase must have passed. No dependency resolution,
baseline build, cache deletion or local authoring-time Lean execution occurs here.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
ROOT_MODULE = "ClassicalMechanicsAssembly"
NATIVE_TARGETS = "Auxillary/assembly-native-targets.txt"
PROOF_TARGETS = "Auxillary/assembly-proof-targets.txt"
SCOPE = "Auxillary/assembly/formalization-status.json"
LOCAL_ROOTS = {
    "ClassicalMechanicsAssembly": "ASSEMBLY",
    "ClassicalMechanics": "Classical_Mechanics_adapter",
    "ClassicalMechanicsForward": "B <-> ClassicalMechanics/=>",
    "ClassicalMechanicsReverse": "B <-> ClassicalMechanics/<=",
    "NSEMaxwell": "Fefferman_adapter",
    "NSEMaxwellForward": "B <-> Maxwell/=>",
    "NSEMaxwellReverse": "B <-> Maxwell/<=",
    "MaxwellEndpoint": "Maxwell_Endpoint",
    "SingularClosure": "Fefferman_adapter/NativeSources/methlib",
    "MethlibEndpoints": "Fefferman_adapter",
}
EXTERNAL_ROOTS = {"Mathlib", "Batteries", "Lean", "Init", "Std", "Aesop", "Qq",
                  "ImportGraph", "ProofWidgets", "LeanSearchClient", "Plausible"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
DECLARATION_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    require(isinstance(data, dict), f"JSON object required: {path}")
    return data


def write_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def targets(path: Path) -> list[str]:
    names = [line.strip() for line in path.read_text(encoding="utf-8-sig").splitlines()
             if line.strip() and not line.lstrip().startswith("#")]
    require(len(names) == len(set(names)), f"Duplicate audit declarations: {path}")
    require(all(DECLARATION_NAME.fullmatch(name) for name in names),
            f"Invalid audit declaration name: {path}")
    return names


def local_closure(root: Path) -> tuple[list[dict], list[str]]:
    """Actual recursive imports, with deterministic topological module order."""
    seen: set[str] = set()
    active: set[str] = set()
    local: list[dict] = []
    external: set[str] = set()

    def visit(module: str) -> None:
        require(MODULE_NAME.fullmatch(module) is not None, f"Invalid import: {module}")
        if module in seen:
            return
        require(module not in active, f"Cyclic module dependency: {module}")
        prefix = module.split(".", 1)[0]
        if prefix in EXTERNAL_ROOTS:
            seen.add(module)
            external.add(module)
            return
        require(prefix in LOCAL_ROOTS, f"Unregistered project import: {module}")
        active.add(module)
        relative = LOCAL_ROOTS[prefix] + "/" + module.replace(".", "/") + ".lean"
        path = root / relative
        require(path.is_file() and not path.is_symlink(), f"Missing native source: {relative}")
        for line in path.read_text(encoding="utf-8-sig").splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                for imported in match.group(1).split("--", 1)[0].split():
                    visit(imported)
        active.remove(module)
        seen.add(module)
        local.append({"module": module, "path": relative, "sha256": digest(path)})

    visit(ROOT_MODULE)
    return local, sorted(external)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external-native-linux", action="store_true", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--dependency-report-directory", type=Path, required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    dependency_report = args.dependency_report_directory.resolve()
    report = args.report_directory.resolve()
    require(report.is_relative_to(root) and report != root, "Report directory must be below the repository root.")
    report.mkdir(parents=True, exist_ok=True)
    provenance = report / "run-provenance.json"
    evidence: dict = {"schema_version": 1, "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                      "stage": "INITIALIZE", "build_status": "NOT_RUN",
                      "audit_command_status": "NOT_RUN", "theorem_axiom_audit_status": "NOT_RUN",
                      "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"}
    timings: list[dict] = []

    def save() -> None:
        write_json(provenance, evidence)
        write_json(report / "command-timings.json", timings)

    def run(command: list[str], log: str, allow_failure: bool = False) -> subprocess.CompletedProcess:
        env = os.environ.copy()
        env["ELAN_TOOLCHAIN"] = TOOLCHAIN
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
        env.pop("LEAN_PATH", None)
        env.pop("LEAN_SRC_PATH", None)
        start = time.monotonic()
        with (report / log).open("w", encoding="utf-8", newline="\n") as stream:
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
        timings.append({"command": command, "log": log, "exit_code": code,
                        "elapsed_seconds": round(time.monotonic() - start, 3)})
        save()
        require(allow_failure or code == 0, f"External command failed ({code}); log={log}")
        return subprocess.CompletedProcess(command, code, "".join(lines))

    try:
        require(args.external_native_linux and sys.platform.startswith("linux"),
                "Explicit external native Linux execution required.")
        require((root / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Wrong toolchain pin.")
        parent = read_json(dependency_report / "run-provenance.json")
        prepared = read_json(dependency_report / "dependency-preparation.json")
        require(parent.get("external_native_linux") is True and parent.get("external_platform") == "linux"
                and parent.get("requested_toolchain") == TOOLCHAIN
                and parent.get("actual_mathlib_commit") == MATHLIB
                and parent.get("dependency_cache_status") == "VERIFIED",
                "The matching external Dependencies phase must pass first.")
        require(prepared.get("status") == "PASS" and prepared.get("external_platform") == "linux",
                "Dependency preparation did not pass.")
        require(parent.get("dependency_preparation_sha256") == digest(dependency_report / "dependency-preparation.json"),
                "Dependency preparation hash mismatch.")
        evidence.update(parent)
        for key in ("failure", "failure_error_id", "failure_stack_trace", "failure_position",
                    "completed_at_utc", "source_manifest_sha256"):
            evidence.pop(key, None)
        evidence.update({"phase": "ASSEMBLY_BUILD_AUDIT", "stage": "VERIFY_INPUTS",
            "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "build_status": "NOT_RUN", "audit_command_status": "NOT_RUN",
            "theorem_axiom_audit_status": "NOT_RUN", "local_lean_executions": 0,
            "baseline_builds": "NOT_INVOKED_BY_ASSEMBLY_RUNNER",
            "cache_mode": "REUSE_VERIFIED_DEPENDENCY_PHASE",
            "parent_dependency_provenance_sha256": digest(dependency_report / "run-provenance.json")})
        linked_reports = [parent.get("native_source_hydration", {})] + parent.get("native_source_closure", [])
        require(len(linked_reports) >= 3, "Hydration and both native source closure reports required.")
        for item in linked_reports:
            name = item.get("report")
            require(isinstance(name, str) and Path(name).name == name, "Invalid dependency evidence path.")
            source = dependency_report / name
            require(source.is_file() and digest(source) == item.get("sha256"), f"Dependency evidence hash mismatch: {name}")
            require(read_json(source).get("status") == "PASS", f"Dependency source check failed: {name}")
            shutil.copyfile(source, report / name)
        shutil.copyfile(dependency_report / "dependency-preparation.json", report / "dependency-preparation.json")
        version = run(["lean", "--version"], "lean-version.log").stdout
        actual = [line.strip() for line in version.splitlines() if re.match(r"^Lean \(version 4\.34\.0-rc1,", line)]
        require(len(actual) == 1 and "-linux-" in actual[0], "Wrong native compiler version or target.")
        evidence["actual_lean_version"] = actual[0]
        require(digest(root / "lake-manifest.json") == parent.get("lockfile_sha256"), "Dependency lock changed.")
        revision = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], "mathlib-revision.log").stdout.strip()
        require(revision == MATHLIB, "Cached Mathlib revision mismatch.")
        commit = run(["git", "rev-parse", "HEAD"], "source-commit.log").stdout.strip()
        require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Missing source commit.")
        if os.environ.get("GITHUB_SHA"):
            require(commit == os.environ["GITHUB_SHA"], "Checkout does not match workflow commit.")
        evidence["source_commit"] = commit
        status = run(["git", "status", "--porcelain", "--untracked-files=no"], "working-tree.log").stdout
        require(not status.strip(), "Tracked sources differ from the external source commit.")

        native = targets(root / NATIVE_TARGETS)
        additional = targets(root / PROOF_TARGETS)
        require(len(native) == 25, "Exactly 25 canonical native endpoint declarations are required.")
        all_targets = native + additional
        require(len(all_targets) == len(set(all_targets)), "Native and proof target lists overlap.")
        generated_targets = report / "audit-targets.txt"
        generated_targets.write_text("\n".join(all_targets) + "\n", encoding="utf-8")
        audit = report / "GeneratedAudit.lean"
        audit.write_text("import ClassicalMechanicsAssembly\n\nset_option pp.universes true\n\n" +
            "\n".join(f"#check @{name}\n#print axioms {name}" for name in all_targets) + "\n", encoding="utf-8")
        closure, external_imports = local_closure(root)
        schedule = [item["module"] for item in closure if item["module"].split(".", 1)[0] == ROOT_MODULE]
        require(schedule and schedule[-1] == ROOT_MODULE, "Assembly module schedule must end at its root.")
        write_json(report / "import-closure.json", {"local_modules": closure,
            "external_imports": external_imports, "assembly_build_schedule": schedule})
        evidence.update({"native_endpoint_count": 25, "additional_proof_target_count": len(additional),
            "audit_target_count": len(all_targets), "module_build_schedule": schedule,
            "import_closure_sha256": digest(report / "import-closure.json"),
            "generated_audit_sha256": digest(audit), "generated_targets_sha256": digest(generated_targets),
            "native_target_list_sha256": digest(root / NATIVE_TARGETS),
            "proof_target_list_sha256": digest(root / PROOF_TARGETS)})

        tracked = subprocess.run(["git", "ls-files", "-z"], cwd=root, check=True,
                                 capture_output=True, text=True).stdout.split("\0")
        active = []
        for relative in tracked:
            if not relative or "/evidence/" in relative:
                continue
            vendor = re.match(r"^(Fefferman_adapter|Maxwell_Endpoint)/NativeSources/([^/]+)/", relative)
            if vendor and vendor.group(2) != "methlib":
                continue
            active.append(relative)
        required = {item["path"] for item in closure} | {
            NATIVE_TARGETS, PROOF_TARGETS, SCOPE, "Auxillary/assembly/run.py",
            "Auxillary/run_assembly.sh", ".github/workflows/classical-assembly.yml"}
        require(required.issubset(active), "An active assembly proof/registry/runner input is untracked.")
        # Generated files are exact deterministic inputs, hashed before compilation.
        active.extend(path.relative_to(root).as_posix() for path in [audit, generated_targets, report / "import-closure.json"])
        entries = []
        for relative in sorted(set(active)):
            path = root / relative
            require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
                    f"Missing, linked or escaping source input: {relative}")
            entries.append({"path": relative, "sha256": digest(path), "size_bytes": path.stat().st_size})
        manifest = report / "source-manifest.json"
        write_json(manifest, {"schema_version": 1, "algorithm": "SHA256", "source_commit": commit,
            "scope": "tracked project/assembly sources plus deterministic generated audit; upstream snapshots verified by linked reports",
            "files": entries})
        evidence["source_manifest_sha256"] = digest(manifest)
        evidence["stage"] = "BUILD"
        save()
        freshness = run(["lake", "build", "--no-build", ROOT_MODULE], "build-freshness.log", allow_failure=True)
        evidence["freshness_check_exit_code"] = freshness.returncode
        evidence["executed_module_builds"] = 0
        if freshness.returncode == 0:
            evidence["build_strategy"] = "LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE"
            shutil.copyfile(report / "build-freshness.log", report / "build.log")
        elif freshness.returncode == 3:
            evidence["build_strategy"] = "SERIAL_INCREMENTAL_ASSEMBLY_REBUILD"
            for module in schedule:
                evidence["current_build_module"] = module
                evidence["executed_module_builds"] += 1
                save()
                run(["lake", "build", module], f"build-{module}.log")
            run(["lake", "build", ROOT_MODULE], "build.log")
        else:
            raise ValueError(f"Lake trace check failed ({freshness.returncode}).")
        evidence["build_status"] = "PASS"
        evidence["stage"] = "FRESH_AXIOM_AUDIT"
        save()
        run(["lake", "env", "lean", "-R", str(report), str(audit)], "audit.log")
        evidence["audit_command_status"] = "PASS"
        evidence["stage"] = "VERIFY_EVIDENCE"
        save()
        run([sys.executable, "Auxillary/scripts/verify_audit.py", "--expected-platform", "linux",
            "--root", str(root), "--targets", str(generated_targets), "--audit-source", str(audit),
            "--log", str(report / "audit.log"), "--manifest", str(manifest),
            "--provenance", str(provenance), "--scope", SCOPE,
            "--output", str(report / "audit-summary.json")], "audit-verifier.log")
        evidence["theorem_axiom_audit_status"] = "PASS_STANDARD_ONLY"
        evidence["stage"] = "COMPLETE"
        evidence["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        save()
        print("ASSEMBLY_EXTERNAL_COMPILER=PASS")
        print("ASSEMBLY_THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY")
        print("SEMANTIC_DISCHARGE=NOT_INFERRED_FROM_AXIOM_AUDIT")
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        evidence["failure"] = str(error)
        evidence["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        save()
        print(f"ASSEMBLY_EXTERNAL_RUN=FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
