#!/usr/bin/env python3
"""Portable native NSE-B/classical-mechanics runner: explicit external Windows execution only."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid


TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
ROOT_MODULE = "ClassicalMechanicsAssembly.FlowNSEBCM"
TARGETS = (
    'ClassicalMechanicsAssembly.nseSolution_iff_cmSolution',
    'ClassicalMechanicsAssembly.nseB_implies_cmB',
    'ClassicalMechanicsAssembly.cmB_implies_nseB',
    'ClassicalMechanicsAssembly.NSEB_IFF_CM',
    'ClassicalMechanicsAssembly.NSEB_IFF_CM_POSITIVE',
)
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external-native-windows", action="store_true", required=True)
    args = parser.parse_args()
    if not args.external_native_windows or sys.platform != "win32":
        raise ValueError("Explicit external native Windows execution required.")
    if sys.version_info < (3, 10):
        raise ValueError("Python >=3.10 required.")
    root = Path(__file__).resolve().parent
    run_id = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8]
    report = root / "artifacts/windows" / run_id
    report.mkdir(parents=True, exist_ok=False)
    evidence: dict = {
        "schema_version": 1, "run_id": run_id,
        "external_platform": "windows", "external_native_windows": True,
        "external_native_linux": False, "requested_toolchain": TOOLCHAIN,
        "build_status": "NOT_RUN", "audit_command_status": "NOT_RUN",
        "theorem_axiom_audit_status": "NOT_RUN",
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
    }
    timings: list[dict] = []

    def save(name: str, value: object) -> None:
        (report / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")

    def run(command: list[str], log: str) -> str:
        env = os.environ.copy()
        env.update(ELAN_TOOLCHAIN=TOOLCHAIN, MATHLIB_NO_CACHE_ON_UPDATE="1")
        env.pop("LEAN_PATH", None)
        env.pop("LEAN_SRC_PATH", None)
        start = time.monotonic()
        with (report / log).open("w", encoding="utf-8", newline="\n") as stream:
            process = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
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
        save("command-timings.json", timings)
        if code:
            raise ValueError(f"Command failed ({code}): {command}; log={log}")
        return "".join(lines).strip()

    try:
        manifest = json.loads((root / "source-manifest.json").read_text(encoding="utf-8"))

        def verify_sources() -> None:
            seen = set()
            for entry in manifest["files"]:
                relative = entry["path"]
                path = (root / relative).resolve()
                if (relative in seen or not path.is_relative_to(root) or not path.is_file()
                        or digest(path) != entry["sha256"]):
                    raise ValueError(f"Export source changed or invalid: {relative}")
                seen.add(relative)
            required = {"lean-toolchain", "lakefile.lean", "lake-manifest.json", "run.py",
                        "run.cmd", "audit_parser.py", "NSEB_IFF_CM.lean", "audit-targets.txt",
                        "NSEB_IFF_CM_A_TIER.txt",
                        "build-targets.json", "cache-targets.json", "formalization-scope.json",
                        "source-map.json", ROOT_MODULE.replace(".", "/") + ".lean"}
            if not required <= seen:
                raise ValueError("Source manifest omits a required export input.")

        verify_sources()
        evidence.update(source_commit=manifest["source_commit"],
                        source_manifest_sha256=digest(root / "source-manifest.json"),
                        source_map_sha256=digest(root / "source-map.json"))
        for name in ("source-manifest.json", "source-map.json", "formalization-scope.json",
                     "audit-targets.txt", "NSEB_IFF_CM.lean", "NSEB_IFF_CM_A_TIER.txt"):
            (report / name).write_bytes((root / name).read_bytes())
        if (root / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise ValueError("Wrong compiler pin.")
        version = run(["lean", "--version"], "lean-version.log")
        if not re.search(r"version 4\.34\.0-rc1,\s*[^,\s]+-windows-[^,\s]+,", version):
            raise ValueError("Matching native Windows Lean 4.34.0-rc1 required.")
        evidence["actual_lean_version"] = version
        lock = json.loads((root / "lake-manifest.json").read_text())
        lock_hash = digest(root / "lake-manifest.json")
        if not any(p["name"] == "mathlib" and p["rev"] == MATHLIB for p in lock["packages"]):
            raise ValueError("Wrong Mathlib pin.")

        def verify_dependency(item: dict, phase: str) -> dict:
            name = item["name"]
            if not re.fullmatch(r"[A-Za-z0-9_-]+", name):
                raise ValueError("Invalid dependency name.")
            dependency = root / ".lake/packages" / name
            revision = run(["git", "-C", str(dependency), "rev-parse", "HEAD"],
                           f"dependency-{name}-{phase}.log")
            if revision != item["rev"]:
                raise ValueError(f"Wrong pinned dependency: {name}; existing checkout preserved.")
            if run(["git", "-C", str(dependency), "status", "--porcelain", "--untracked-files=no"],
                   f"dependency-{name}-{phase}-status.log"):
                raise ValueError(f"Modified dependency: {name}; existing checkout preserved.")
            return {"name": name, "revision": revision}

        # Reject mismatched existing checkouts before Lake can resolve missing dependencies.
        for item in lock["packages"]:
            if (root / ".lake/packages" / item["name"]).exists():
                verify_dependency(item, "existing")
        run(["lake", "env", "lean", "--version"], "dependency-resolution.log")
        evidence["dependency_revisions"] = [verify_dependency(p, "resolved") for p in lock["packages"]]
        evidence["actual_mathlib_commit"] = MATHLIB
        cache_targets = json.loads((root / "cache-targets.json").read_text())
        if not cache_targets or any(not MODULE.fullmatch(m) or
                not (m == "Mathlib" or m.startswith("Mathlib.")) for m in cache_targets):
            raise ValueError("Invalid Mathlib cache target set.")
        run(["lake", "exe", "cache", "get", "--cache-from=master,legacy", *cache_targets], "cache.log")
        if digest(root / "lake-manifest.json") != lock_hash:
            raise ValueError("Dependency preparation changed the pinned lockfile.")
        for module in cache_targets:
            if not (root / ".lake/packages/mathlib/.lake/build/lib/lean" /
                    (module.replace(".", "/") + ".olean")).is_file():
                raise ValueError(f"Required official Mathlib cache missing: {module}")
        evidence["cache_mode"] = "PRESERVED_OBJECTS_AND_OFFICIAL_INCREMENTAL_CACHE_GET"
        modules = json.loads((root / "build-targets.json").read_text())
        if (not modules or modules[-1] != ROOT_MODULE or len(set(modules)) != len(modules)
                or any(not MODULE.fullmatch(m) for m in modules)):
            raise ValueError("Invalid deterministic module schedule.")
        for module in modules:
            run(["lake", "build", module], f"build-{module}.log")
        evidence["build_status"] = "PASS"
        # Direct source execution prints fresh records; no compiled audit module is reused.
        log = run(["lake", "env", "lean", "NSEB_IFF_CM.lean"], "audit.log")
        evidence["audit_command_status"] = "PASS"
        spec = importlib.util.spec_from_file_location("audit_parser", root / "audit_parser.py")
        assert spec is not None and spec.loader is not None
        audit = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(audit)
        targets = audit.parse_targets(root / "audit-targets.txt")
        if tuple(targets) != TARGETS:
            raise ValueError("Exact native root target list changed.")
        source = (root / "NSEB_IFF_CM.lean").read_text()
        for pattern in (r"^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
                        r"^\s*#check\s+@([A-Za-z_][A-Za-z0-9_'.]*)\s*$"):
            if re.findall(pattern, source, re.MULTILINE) != targets:
                raise ValueError("Audit source must check and print every exact root once.")
        if "sorryAx" in log or re.search(r"declaration uses ['\u2018]sorry|(?:^|\n).*:\s*error:", log):
            raise ValueError("Admission or compiler error in fresh audit.")
        records = audit.parse_axioms(log)
        theorems = []
        for target in targets:
            values = records.get(target, [])
            if len(values) != 1:
                raise ValueError(f"Expected one fresh axiom record: {target}")
            axioms = sorted(audit.normalize_axiom_name(name) for name in values[0])
            if set(axioms) - {"propext", "Classical.choice", "Quot.sound"}:
                raise ValueError(f"Unapproved axiom: {target}: {axioms}")
            theorems.append({"name": target, "axioms": axioms, "status": "PASS_STANDARD_ONLY"})
        verify_sources()
        if digest(root / "source-manifest.json") != evidence["source_manifest_sha256"]:
            raise ValueError("Source manifest changed during external validation.")
        evidence.update(status="PASS", source_input_verification="PASS",
                        theorem_axiom_audit_status="PASS_STANDARD_ONLY")
        save("audit-summary.json", {**evidence, "theorems": theorems,
             "exact_root_promotion": "REQUIRES_SEPARATE_SCOPE_AND_PREMISE_REVIEW"})
        print(f"EXTERNAL_WINDOWS_COMPILER=PASS; THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY; REPORT={report}")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        evidence.update(status="FAIL", failure=str(error))
        print(f"EXTERNAL_WINDOWS_VALIDATION=FAIL: {error}", file=sys.stderr)
        return 1
    finally:
        save("run-provenance.json", evidence)


if __name__ == "__main__":
    raise SystemExit(main())
