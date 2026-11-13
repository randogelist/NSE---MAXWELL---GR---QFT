#!/usr/bin/env python3
"""Build and freshly audit the mechanics chain on an external cached Linux host.

The Dependencies phase of Auxillary/run.sh must have completed first.  This
runner neither acquires dependencies nor removes any compiler/build cache.
It runs before the unchanged baseline integrated and isolated package checks.
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
SOURCE_ROOT = "Classical_Mechanics_adapter"
FORWARD_ROOT = "B <-> ClassicalMechanics/=>"
REVERSE_ROOT = "B <-> ClassicalMechanics/<="
TARGETS = "Auxillary/classical-mechanics-audit-targets.txt"
SCOPE = "Auxillary/classical-mechanics-status.json"
AUDIT = f"{SOURCE_ROOT}/ClassicalMechanics/Audit.lean"
MODULES = [
    "ClassicalMechanics.Stress",
    "ClassicalMechanics.Definitions",
    "ClassicalMechanics.FiniteSlab",
    "ClassicalMechanicsForward",
    "ClassicalMechanicsReverse",
    "ClassicalMechanics.Equivalence",
    "ClassicalMechanics.MaxwellBridge",
    "ClassicalMechanics",
]
AGGREGATES = ["ClassicalMechanics", "ClassicalMechanicsForward", "ClassicalMechanicsReverse"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8-sig"))
    require(isinstance(value, dict), f"JSON object required: {path}")
    return value


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def module_source(module: str) -> str:
    if module == "ClassicalMechanicsForward" or module.startswith("ClassicalMechanicsForward."):
        prefix = FORWARD_ROOT
    elif module == "ClassicalMechanicsReverse" or module.startswith("ClassicalMechanicsReverse."):
        prefix = REVERSE_ROOT
    else:
        prefix = SOURCE_ROOT
    return prefix + "/" + module.replace(".", "/") + ".lean"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external-native-linux", action="store_true", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--report-directory", type=Path, required=True)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    report = args.report_directory.resolve()
    report.mkdir(parents=True, exist_ok=True)
    baseline = report.parent
    provenance_path = report / "run-provenance.json"
    commands: list[dict] = []
    evidence: dict = {
        "schema_version": 1,
        "started_at_utc": now(),
        "stage": "INITIALIZE",
        "build_status": "NOT_RUN",
        "audit_command_status": "NOT_RUN",
        "theorem_axiom_audit_status": "NOT_RUN",
        "exact_root_promotion": "NOT_AUTOMATIC",
    }

    def save() -> None:
        write_json(provenance_path, evidence)
        write_json(report / "command-timings.json", commands)

    def run(command: list[str], log: str, allow_failure: bool = False) -> subprocess.CompletedProcess:
        started = now()
        tick = time.monotonic()
        env = os.environ.copy()
        env["ELAN_TOOLCHAIN"] = TOOLCHAIN
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
        env.pop("LEAN_PATH", None)
        env.pop("LEAN_SRC_PATH", None)
        with (report / log).open("w", encoding="utf-8", newline="\n") as stream:
            process = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                                       errors="replace", bufsize=1)
            lines: list[str] = []
            assert process.stdout is not None
            for line in process.stdout:
                lines.append(line)
                stream.write(line)
                stream.flush()
                print(line, end="", flush=True)
            code = process.wait()
        commands.append({"command": command, "log": log, "started_at_utc": started,
                         "elapsed_seconds": round(time.monotonic() - tick, 3), "exit_code": code})
        save()
        require(allow_failure or code == 0, f"External command failed ({code}); log={log}")
        return subprocess.CompletedProcess(command, code, "".join(lines))

    try:
        require(args.external_native_linux and sys.platform.startswith("linux"),
                "Explicit external native Linux execution is required.")
        require((root / "lean-toolchain").read_text().strip() == TOOLCHAIN,
                "The active toolchain differs from the frozen compiler.")
        parent = read_json(baseline / "run-provenance.json")
        prepared = read_json(baseline / "dependency-preparation.json")
        require(parent.get("external_native_linux") is True and
                parent.get("external_platform") == "linux" and
                parent.get("requested_toolchain") == TOOLCHAIN and
                parent.get("actual_mathlib_commit") == MATHLIB and
                parent.get("dependency_cache_status") == "VERIFIED",
                "The matching external dependency phase has not passed.")
        require(prepared.get("status") == "PASS" and prepared.get("external_platform") == "linux",
                "A successful pinned dependency preparation record is required.")
        require(parent.get("dependency_preparation_sha256") ==
                digest(baseline / "dependency-preparation.json"),
                "The dependency preparation report hash differs from its provenance.")
        evidence.update(parent)
        for key in ("failure", "failure_error_id", "failure_stack_trace", "failure_position",
                    "completed_at_utc", "source_manifest_sha256"):
            evidence.pop(key, None)
        evidence.update({
            "started_at_utc": now(), "phase": "CLASSICAL_MECHANICS_BUILD_AUDIT",
            "stage": "VERIFY_PINNED_INPUTS", "build_status": "NOT_RUN",
            "audit_command_status": "NOT_RUN", "theorem_axiom_audit_status": "NOT_RUN",
            "cache_mode": "REUSE_VERIFIED_DEPENDENCY_PHASE",
            "module_build_schedule": MODULES, "aggregate_build_targets": AGGREGATES,
            "module_build_concurrency": 1, "local_lean_executions": 0,
            "baseline_package_validation": "UNCHANGED_WORKFLOW_STEPS_FOLLOW",
            "parent_dependency_provenance_sha256": digest(baseline / "run-provenance.json"),
        })
        save()

        # Preserve the exact evidence objects consumed by the common verifier.
        reports = [parent.get("native_source_hydration", {})] + parent.get("native_source_closure", [])
        require(len(reports) >= 3, "Hydration and both native source closure reports are required.")
        for record in reports:
            name = record.get("report")
            require(isinstance(name, str) and Path(name).name == name, "Invalid dependency report name.")
            source = baseline / name
            require(source.is_file() and digest(source) == record.get("sha256"),
                    f"Dependency evidence hash mismatch: {name}")
            require(read_json(source).get("status") == "PASS", f"Dependency source check failed: {name}")
            shutil.copyfile(source, report / name)
        shutil.copyfile(baseline / "dependency-preparation.json", report / "dependency-preparation.json")

        version = run(["lean", "--version"], "lean-version.log").stdout
        version_lines = [line.strip() for line in version.splitlines()
                         if re.match(r"^Lean \(version 4\.34\.0-rc1,", line)]
        require(len(version_lines) == 1 and "-linux-" in version_lines[0],
                "The actual external compiler target is not native Linux Lean 4.34.0-rc1.")
        evidence["actual_lean_version"] = version_lines[0]
        revision = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                       "mathlib-revision.log").stdout.strip()
        require(revision == MATHLIB, "The restored Mathlib dependency changed.")
        require(digest(root / "lake-manifest.json") == parent.get("lockfile_sha256"),
                "The dependency lock changed after preparation.")
        commit = run(["git", "rev-parse", "HEAD"], "source-commit.log").stdout.strip()
        require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Missing exact source commit.")
        if os.environ.get("GITHUB_SHA"):
            require(commit == os.environ["GITHUB_SHA"], "Checkout does not match the workflow source commit.")
        evidence["source_commit"] = commit
        status = run(["git", "status", "--porcelain", "--untracked-files=no"], "working-tree.log").stdout
        require(not status.strip(), "Tracked source files differ from the workflow commit.")

        required = [module_source(module) for module in MODULES] + [AUDIT, TARGETS, SCOPE]
        for relative in required:
            path = root / relative
            require(path.is_file() and not path.is_symlink(), f"Missing mechanics input: {relative}")
        tracked = subprocess.run(["git", "ls-files", "-z"], cwd=root, check=True,
                                 capture_output=True, text=True).stdout.split("\0")
        active: list[str] = []
        for relative in tracked:
            if not relative or relative.startswith("Auxillary/evidence/"):
                continue
            # These complete pinned source trees have just been checked against
            # Git identities by the dependency phase. Their signed/hash-linked
            # manifests are retained here; repeated vendor-byte hashing is not
            # necessary for the targeted native project theorem certificate.
            match = re.match(r"^(Fefferman_adapter|Maxwell_Endpoint)/NativeSources/([^/]+)/", relative)
            if match and match.group(2) != "methlib":
                continue
            active.append(relative)
        require(set(required).issubset(active), "An active mechanics proof or audit input is untracked.")
        entries = []
        for relative in sorted(set(active)):
            path = root / relative
            require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
                    f"Missing, linked or escaping tracked source input: {relative}")
            entries.append({"path": relative, "sha256": digest(path), "size_bytes": path.stat().st_size})
        manifest = report / "source-manifest.json"
        write_json(manifest, {"schema_version": 1, "algorithm": "SHA256", "source_commit": commit,
                              "scope": "tracked project inputs; full upstream snapshots verified by linked native-source reports",
                              "files": entries})
        evidence["source_manifest_sha256"] = digest(manifest)
        evidence["mechanics_source_paths"] = required
        evidence["audit_targets_path"] = TARGETS
        evidence["audit_source_path"] = AUDIT
        evidence["stage"] = "BUILD"
        save()

        freshness = run(["lake", "build", "--no-build", *AGGREGATES],
                        "run-build-freshness.log", allow_failure=True)
        evidence["freshness_check_exit_code"] = freshness.returncode
        evidence["executed_module_builds"] = 0
        if freshness.returncode == 0:
            evidence["build_strategy"] = "LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE"
            shutil.copyfile(report / "run-build-freshness.log", report / "run-build.log")
        elif freshness.returncode == 3:
            evidence["build_strategy"] = "SERIAL_INCREMENTAL_REBUILD"
            for module in MODULES:
                evidence["current_build_module"] = module
                evidence["executed_module_builds"] += 1
                save()
                run(["lake", "build", module], "run-build-" + module.replace(".", "-") + ".log")
            run(["lake", "build", *AGGREGATES], "run-build.log")
        else:
            raise ValueError(f"Lake trace freshness check failed with exit code {freshness.returncode}.")
        evidence["build_status"] = "PASS"
        evidence["stage"] = "AXIOM_AUDIT"
        save()
        # This command is fresh even when every project object was cached.
        run(["lake", "env", "lean", "-R", SOURCE_ROOT, AUDIT], "run-audit.log")
        evidence["audit_command_status"] = "PASS"
        evidence["stage"] = "VERIFY_EVIDENCE"
        save()
        run([sys.executable, "Auxillary/scripts/verify_audit.py",
             "--expected-platform", "linux", "--root", str(root),
             "--targets", TARGETS, "--audit-source", AUDIT,
             "--log", str(report / "run-audit.log"), "--manifest", str(manifest),
             "--provenance", str(provenance_path), "--scope", SCOPE,
             "--output", str(report / "audit-summary.json")], "audit-verifier.log")
        evidence["theorem_axiom_audit_status"] = "PASS_STANDARD_ONLY"
        evidence["stage"] = "COMPLETE"
        evidence["completed_at_utc"] = now()
        save()
        print("CLASSICAL_MECHANICS_EXTERNAL_COMPILER=PASS")
        print("CLASSICAL_MECHANICS_AXIOM_AUDIT=PASS_STANDARD_ONLY")
        print("EXACT_ROOT_PROMOTION=REQUIRES_SCOPE_AND_PREMISE_REVIEW")
        return 0
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        evidence["failure"] = str(error)
        evidence["completed_at_utc"] = now()
        save()
        print(f"CLASSICAL_MECHANICS_EXTERNAL_RUN=FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
