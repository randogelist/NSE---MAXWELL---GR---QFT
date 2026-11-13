#!/usr/bin/env python3
"""External compatibility-route audit with zero custom axioms for all five theorems.

The preceding 43-target standard-only assembly audit must pass unchanged.
This runner never broadens the common verifier's foundational axiom allowlist.
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


TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
POLICY = "Auxillary/assembly/literature-targets.json"
STATUS = "Auxillary/assembly/literature-status.json"
PREFIX = "ClassicalMechanicsAssembly.Literature."
FOUNDATIONS = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXACT_POLICY = {
    PREFIX + "L1": frozenset(),
    PREFIX + "L2": frozenset(),
    PREFIX + "L2_native": frozenset(),
    PREFIX + "CLASSICAL_MECHANICS_MATERIAL_FROM_L1_L2": frozenset(),
    PREFIX + "CLASSICAL_MECHANICS_MATERIAL_FROM_L1": frozenset(),
}
MODULES = ["ClassicalMechanicsAssembly.LiteratureInputs",
           "ClassicalMechanicsAssembly.LiteratureClosure"]


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


def import_helper(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f"Cannot load helper: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_policy(policy: dict) -> list[str]:
    require(policy.get("schema_version") == 1 and policy.get("exact_nonfoundational_policy") is True,
            "Exact literature axiom policy required.")
    require(set(policy.get("foundational_axioms", [])) == FOUNDATIONS,
            "The foundational axiom policy must remain unchanged.")
    require(policy.get("authorized_axiom_declarations") == [],
            "No custom axiom declarations are authorized; all five contracts must be native theorems.")
    targets = policy.get("targets", [])
    require(isinstance(targets, list) and len(targets) == 5, "Exactly five literature audit targets required.")
    names = [item["name"] for item in targets]
    require(len(set(names)) == 5 and names == list(EXACT_POLICY), "Exact ordered target declarations differ.")
    for item in targets:
        actual = item.get("expected_nonfoundational_axioms", [])
        require(isinstance(actual, list) and len(actual) == len(set(actual))
                and frozenset(actual) == EXACT_POLICY[item["name"]],
                f"Exact axiom policy differs: {item['name']}")
        expected_kind = "theorem"
        require(item.get("kind") == expected_kind, f"Wrong declaration kind: {item['name']}")
    return names


def verify_target_axioms(log: str, audit_source: str, policy: dict, parser_module) -> list[dict]:
    names = validate_policy(policy)
    require(parser_module.ALLOWED_AXIOMS == FOUNDATIONS, "The shared standard-only allowlist changed.")
    require("sorryAx" not in log and not re.search(
        r"declaration uses ['\u2018]sorry|(?:^|\n).*:\s*error:", log), "Audit contains an admission or compiler error.")
    for pattern in [r"^\s*#check\s+@?([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$",
                    r"^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$"]:
        found = re.findall(pattern, audit_source, re.MULTILINE)
        require(len(found) == 5 and found == names, "Generated signatures/axiom directives differ from policy.")
    records = parser_module.parse_axioms(log)
    require(set(records) == set(names), "Compiler axiom record set differs from the exact policy.")
    result = []
    for name in names:
        require(len(records[name]) == 1, f"Expected one fresh axiom record: {name}")
        actual = {parser_module.normalize_axiom_name(item) for item in records[name][0]}
        extra = actual - FOUNDATIONS
        require(extra == EXACT_POLICY[name],
                f"Exact nonfoundational axiom mismatch for {name}: actual={sorted(extra)}; expected={sorted(EXACT_POLICY[name])}")
        require(re.search(r"(?:^|\n)@?" + re.escape(name) + r"\s*:", log) is not None,
                f"Full printed declaration signature absent: {name}")
        result.append({"name": name,
            "status": "PASS_STANDARD_ONLY",
            "axioms": sorted(actual), "foundational_axioms": sorted(actual & FOUNDATIONS),
            "nonfoundational_axioms": sorted(extra),
            "expected_nonfoundational_axioms": sorted(EXACT_POLICY[name])})
    return result


def import_closure(root: Path, helper) -> list[dict]:
    seen: set[str] = set()
    active: set[str] = set()
    result = []

    def visit(module: str) -> None:
        require(helper.MODULE_NAME.fullmatch(module) is not None, f"Invalid module import: {module}")
        if module in seen:
            return
        prefix = module.split(".", 1)[0]
        if prefix in helper.EXTERNAL_ROOTS:
            seen.add(module)
            return
        require(prefix in helper.LOCAL_ROOTS and module not in active, f"Unknown/cyclic local import: {module}")
        active.add(module)
        relative = helper.LOCAL_ROOTS[prefix] + "/" + module.replace(".", "/") + ".lean"
        path = root / relative
        require(path.is_file() and not path.is_symlink(), f"Missing local source: {relative}")
        for line in path.read_text(encoding="utf-8-sig").splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                for dependency in match.group(1).split("--", 1)[0].split():
                    visit(dependency)
        active.remove(module)
        seen.add(module)
        result.append({"module": module, "path": relative, "sha256": digest(path)})

    visit(MODULES[-1])
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external-native-linux", action="store_true", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--standard-report-directory", type=Path, required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    args = parser.parse_args()
    root, standard, report = args.repo_root.resolve(), args.standard_report_directory.resolve(), args.report_directory.resolve()
    require(report.is_relative_to(root) and report != root and report != standard,
            "A distinct report directory below the repository root is required.")
    report.mkdir(parents=True, exist_ok=True)
    evidence: dict = {"schema_version": 1, "stage": "INITIALIZE", "build_status": "NOT_RUN",
        "audit_command_status": "NOT_RUN", "theorem_axiom_audit_status": "NOT_RUN",
        "semantic_discharge": 'L1_AND_L2_NATIVE; NO_CUSTOM_AXIOMS; EXACT_SUPPLIED_VELOCITY_FINITE_SLAB_SCOPE'}
    timings: list[dict] = []

    def save() -> None:
        write_json(report / "run-provenance.json", evidence)
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
        require(args.external_native_linux and sys.platform.startswith("linux"), "Explicit external native Linux required.")
        helper = import_helper(root / "Auxillary/assembly/run.py", "assembly_source_helper")
        axiom_parser = import_helper(root / "Auxillary/scripts/verify_audit.py", "standard_axiom_parser")
        require(axiom_parser.ALLOWED_AXIOMS == FOUNDATIONS, "The shared standard-only axiom allowlist changed.")
        policy = read_json(root / POLICY)
        names = validate_policy(policy)
        parent = read_json(standard / "run-provenance.json")
        prior_audit = read_json(standard / "audit-summary.json")
        prior_manifest = read_json(standard / "source-manifest.json")
        require(parent.get("build_status") == parent.get("audit_command_status") == "PASS"
                and parent.get("theorem_axiom_audit_status") == prior_audit.get("status") == "PASS_STANDARD_ONLY",
                "The independent standard-only assembly audit must pass first.")
        require(parent.get("audit_target_count") == 43 and len(prior_audit.get("theorems", [])) == 43
                and all(item.get("status") == "PASS_STANDARD_ONLY" and
                        set(item.get("axioms", [])) <= FOUNDATIONS for item in prior_audit["theorems"]),
                "The unchanged 43-target standard-only audit is required.")
        require(parent.get("external_native_linux") is True and parent.get("requested_toolchain") == TOOLCHAIN
                and parent.get("actual_mathlib_commit") == MATHLIB and parent.get("dependency_cache_status") == "VERIFIED",
                "Matching external cached native compiler/dependency evidence required.")
        require(digest(standard / "source-manifest.json") == parent.get("source_manifest_sha256") == prior_audit.get("source_manifest_sha256"),
                "Standard source-manifest hash mismatch.")
        require(parent.get("source_commit") == prior_audit.get("source_commit") == prior_manifest.get("source_commit"),
                "Standard source-commit mismatch.")
        require(digest(root / "lake-manifest.json") == parent.get("lockfile_sha256"), "Dependency lock changed.")
        evidence.update(parent)
        evidence.update({"phase": "LITERATURE_BUILD_AUDIT", "stage": "VERIFY_INPUTS",
            "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "build_status": "NOT_RUN", "audit_command_status": "NOT_RUN",
            "theorem_axiom_audit_status": "NOT_RUN", "audit_target_count": 5,
            "native_endpoint_count": 0, "additional_proof_target_count": 0,
            "authorized_axiom_declaration_count": 0, "literature_theorem_count": 5,
            "module_build_schedule": MODULES, "local_lean_executions": 0,
            "semantic_discharge": 'L1_AND_L2_NATIVE; NO_CUSTOM_AXIOMS; EXACT_SUPPLIED_VELOCITY_FINITE_SLAB_SCOPE',
            "standard_43_audit_summary_sha256": digest(standard / "audit-summary.json"),
            "standard_43_source_manifest_sha256": digest(standard / "source-manifest.json"),
            "standard_43_provenance_sha256": digest(standard / "run-provenance.json"),
            "literature_policy_path": POLICY, "literature_policy_sha256": digest(root / POLICY),
            "shared_foundational_allowlist_unchanged": True})
        for key in ("completed_at_utc", "failure", "source_manifest_sha256", "generated_audit_sha256",
                    "generated_targets_sha256", "current_build_module", "import_closure_sha256",
                    "native_target_list_sha256", "proof_target_list_sha256"):
            evidence.pop(key, None)
        save()
        version = run(["lean", "--version"], "lean-version.log").stdout.strip()
        require(version == parent.get("actual_lean_version") and re.search(
            r"version 4\.34\.0-rc1,\s*[^,\s]+-linux-[^,\s]+,", version) is not None,
            "External compiler changed after the strict standard audit.")
        commit = run(["git", "rev-parse", "HEAD"], "source-commit.log").stdout.strip()
        require(commit == parent.get("source_commit") and
                (not os.environ.get("GITHUB_SHA") or commit == os.environ["GITHUB_SHA"]), "Source commit changed.")
        require(not run(["git", "status", "--porcelain", "--untracked-files=no"], "working-tree.log").stdout.strip(),
                "Tracked source modifications after the standard audit.")
        require(run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], "mathlib-revision.log").stdout.strip() == MATHLIB,
                "Mathlib revision changed.")
        for record in [parent["native_source_hydration"], *parent["native_source_closure"]]:
            name = record["report"]
            require(Path(name).name == name and digest(standard / name) == record["sha256"]
                    and read_json(standard / name).get("status") == "PASS", "Native dependency evidence changed.")
            shutil.copyfile(standard / name, report / name)

        original_files = {item["path"]: item for item in prior_manifest["files"]}
        require(len(original_files) == len(prior_manifest["files"]), "Duplicate standard manifest inputs.")
        for relative, item in original_files.items():
            path = (root / relative).resolve()
            require(path.is_relative_to(root) and path.is_file() and not path.is_symlink()
                    and digest(path) == item["sha256"], f"Standard source input changed: {relative}")
        closure = import_closure(root, helper)
        cache_targets = set()
        for entry in closure:
            for line in (root / entry["path"]).read_text(encoding="utf-8-sig").splitlines():
                match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
                if match:
                    cache_targets.update(name for name in match.group(1).split("--", 1)[0].split()
                        if name == "Mathlib" or name.startswith("Mathlib."))
        require(cache_targets, "Native compatibility closure has no Mathlib cache imports.")
        run(["lake", "exe", "cache", "get", "--cache-from=master,legacy", *sorted(cache_targets)],
            "incremental-mathlib-cache.log")
        for name in cache_targets:
            require((root / ".lake/packages/mathlib/.lake/build/lib/lean" /
                     (name.replace(".", "/") + ".olean")).is_file(), f"Missing cached import: {name}")
        require(digest(root / "lake-manifest.json") == parent["lockfile_sha256"],
                "Incremental cache preparation changed the pinned lockfile.")
        evidence["cache_mode"] = "PRESERVED_OBJECTS_AND_OFFICIAL_INCREMENTAL_CACHE_GET"
        required = {item["path"] for item in closure} | {
            POLICY, STATUS, "Auxillary/assembly/run_literature.py", "Auxillary/run_literature.sh",
            ".github/workflows/classical-assembly.yml", "AGENTS.md"}
        require(required.issubset(original_files), "Literature sources/policy/runner/status are missing from the committed standard source manifest.")
        audit = report / "LiteratureAudit.lean"
        audit.write_text("import ClassicalMechanicsAssembly.LiteratureClosure\n\nset_option pp.universes true\n\n" +
            "\n".join(f"#check @{name}\n#print axioms {name}" for name in names) + "\n", encoding="utf-8")
        (report / "audit-targets.txt").write_text("\n".join(names) + "\n", encoding="utf-8")
        write_json(report / "import-closure.json", {"local_modules": closure, "module_build_schedule": MODULES})
        write_json(report / "axiom-policy.json", policy)
        entries = list(original_files.values())
        for path in [audit, report / "audit-targets.txt", report / "import-closure.json", report / "axiom-policy.json"]:
            entries.append({"path": path.relative_to(root).as_posix(), "sha256": digest(path), "size_bytes": path.stat().st_size})
        manifest = report / "source-manifest.json"
        write_json(manifest, {"schema_version": 1, "source_commit": commit,
            "scope": "all unchanged standard assembly source inputs plus isolated literature audit and exact per-target policy",
            "files": sorted(entries, key=lambda item: item["path"])})
        evidence.update({"source_manifest_sha256": digest(manifest), "generated_audit_sha256": digest(audit),
            "import_closure_sha256": digest(report / "import-closure.json"), "stage": "BUILD"})
        save()
        fresh = run(["lake", "build", "--no-build", MODULES[-1]], "build-freshness.log", allow_failure=True)
        evidence["freshness_check_exit_code"] = fresh.returncode
        evidence["executed_module_builds"] = 0
        if fresh.returncode == 0:
            evidence["build_strategy"] = "LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE"
            shutil.copyfile(report / "build-freshness.log", report / "build.log")
        elif fresh.returncode == 3:
            evidence["build_strategy"] = "SERIAL_INCREMENTAL_LITERATURE_REBUILD"
            for module in MODULES:
                evidence["current_build_module"] = module
                evidence["executed_module_builds"] += 1
                save()
                run(["lake", "build", module], f"build-{module}.log")
            run(["lake", "build", MODULES[-1]], "build.log")
        else:
            raise ValueError(f"Lake trace freshness check failed ({fresh.returncode}).")
        evidence["build_status"] = "PASS"
        evidence["stage"] = "FRESH_EXACT_AXIOM_AUDIT"
        save()
        log = run(["lake", "env", "lean", "-R", str(report), str(audit)], "audit.log").stdout
        evidence["audit_command_status"] = "PASS"
        records = verify_target_axioms(log, audit.read_text(encoding="utf-8"), policy, axiom_parser)
        for item in entries:
            require(digest(root / item["path"]) == item["sha256"], f"Source input changed during compilation: {item['path']}")
        require(digest(standard / "audit-summary.json") == evidence["standard_43_audit_summary_sha256"]
                and digest(standard / "run-provenance.json") == evidence["standard_43_provenance_sha256"],
                "Independent standard-only audit evidence changed.")
        write_json(report / "audit-summary.json", {
            "schema_version": 1, "status": "PASS_STANDARD_ONLY", "source_commit": commit,
            "source_manifest_sha256": digest(manifest), "axiom_policy_sha256": digest(root / POLICY),
            "external_compiler_status": "PASS", "audit_command_status": "PASS", "source_input_verification": "PASS",
            "expected_platform": "linux", "actual_lean_version": version, "mathlib_commit": MATHLIB,
            "foundational_axioms": sorted(FOUNDATIONS), "authorized_axiom_declarations": [],
            "exact_nonfoundational_policy": True, "targets": records, "errors": [],
            "standard_43_audit_summary_sha256": evidence["standard_43_audit_summary_sha256"],
            "standard_43_audit_status": "PASS_STANDARD_ONLY",
            "semantic_discharge": 'L1_AND_L2_NATIVE; NO_CUSTOM_AXIOMS; EXACT_SUPPLIED_VELOCITY_FINITE_SLAB_SCOPE',
            "L2_elimination": "L1_L2_L2_NATIVE_AND_BOTH_COMPATIBILITY_ROOTS_STANDARD_ONLY",
            "full_solution_set_bijection": "NOT_ASSERTED"})
        evidence["theorem_axiom_audit_status"] = "PASS_STANDARD_ONLY"
        evidence["stage"] = "COMPLETE"
        evidence["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        save()
        print("LITERATURE_EXTERNAL_COMPILER=PASS")
        print("LITERATURE_AXIOM_AUDIT=PASS_STANDARD_ONLY")
        print("STANDARD_ASSEMBLY_43=PASS_STANDARD_ONLY_UNCHANGED")
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        evidence["failure"] = str(error)
        evidence["completed_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        save()
        write_json(report / "audit-summary.json", {"status": "FAIL", "errors": [str(error)],
            "semantic_discharge": 'L1_AND_L2_NATIVE; NO_CUSTOM_AXIOMS; EXACT_SUPPLIED_VELOCITY_FINITE_SLAB_SCOPE'})
        print(f"LITERATURE_EXTERNAL_RUN=FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
