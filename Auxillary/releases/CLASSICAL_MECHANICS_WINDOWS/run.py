#!/usr/bin/env python3
"""Copied into the portable source export as run.py; external Windows execution only."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external-native-windows", action="store_true", required=True)
    args = parser.parse_args()
    if not args.external_native_windows or sys.platform != "win32":
        raise ValueError("Explicit external native Windows execution required.")
    root = Path(__file__).resolve().parent
    os.chdir(root)
    report = root / "artifacts/windows"
    report.mkdir(parents=True, exist_ok=True)
    evidence: dict = {"schema_version": 1, "external_platform": "windows",
                      "build_status": "NOT_RUN", "audit_command_status": "NOT_RUN",
                      "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"}
    timings = []

    def save(name: str, value: object) -> None:
        (report / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")

    def run(command: list[str], log: str) -> str:
        env = os.environ.copy()
        env["ELAN_TOOLCHAIN"] = TOOLCHAIN
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
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
            raise ValueError(f"External command failed ({code}): {command}; log={log}")
        return "".join(lines).strip()

    try:
        manifest = json.loads((root / "source-manifest.json").read_text())

        def verify_sources() -> None:
            seen = set()
            for entry in manifest["files"]:
                relative = entry["path"]
                path = (root / relative).resolve()
                if relative in seen or not path.is_relative_to(root) or not path.is_file() or digest(path) != entry["sha256"]:
                    raise ValueError(f"Exported source changed or invalid: {relative}")
                seen.add(relative)

        verify_sources()
        evidence["source_commit"] = manifest["source_commit"]
        evidence["source_manifest_sha256"] = digest(root / "source-manifest.json")
        evidence["source_map_sha256"] = digest(root / "source-map.json")
        if (root / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise ValueError("Wrong compiler pin.")
        version = run(["lean", "--version"], "lean-version.log")
        if not re.search(r"version 4\.34\.0-rc1,\s*[^,\s]+-windows-[^,\s]+,", version):
            raise ValueError("Matching native Windows Lean 4.34.0-rc1 required.")
        evidence["actual_lean_version"] = version
        lock = json.loads((root / "lake-manifest.json").read_text())
        lock_hash = digest(root / "lake-manifest.json")
        if not any(item["name"] == "mathlib" and item["rev"] == MATHLIB for item in lock["packages"]):
            raise ValueError("Wrong Mathlib pin.")
        # Resolve the committed lockfile once; never run `lake update` or clean.
        run(["lake", "env", "lean", "--version"], "dependency-resolution.log")
        revisions = []
        for item in lock["packages"]:
            name = item["name"]
            if not re.fullmatch(r"[A-Za-z0-9_-]+", name):
                raise ValueError("Invalid dependency name.")
            dependency = root / ".lake/packages" / name
            revision = run(["git", "-C", str(dependency), "rev-parse", "HEAD"], f"dependency-{name}.log")
            if revision != item["rev"]:
                raise ValueError(f"Wrong pinned dependency: {name}")
            if run(["git", "-C", str(dependency), "status", "--porcelain", "--untracked-files=no"], f"dependency-{name}-status.log"):
                raise ValueError(f"Modified pinned dependency: {name}")
            revisions.append({"name": name, "revision": revision})
        evidence["dependency_revisions"] = revisions
        evidence["actual_mathlib_commit"] = MATHLIB
        run(["lake", "exe", "cache", "get", "--cache-from=master,legacy", "Mathlib"], "cache.log")
        if digest(root / "lake-manifest.json") != lock_hash:
            raise ValueError("Dependency preparation changed the pinned lockfile.")
        if not (root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file():
            raise ValueError("Required official Mathlib cache missing.")
        evidence["cache_mode"] = "PRESERVED_OBJECTS_AND_OFFICIAL_INCREMENTAL_CACHE_GET"
        modules = json.loads((root / "build-targets.json").read_text())
        if not modules or len(set(modules)) != len(modules) or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", m) for m in modules):
            raise ValueError("Invalid deterministic module schedule.")
        for module in modules:
            run(["lake", "build", module], f"build-{module}.log")
        evidence["build_status"] = "PASS"
        log = run(["lake", "env", "lean", "ClassicalMechanics/Audit.lean"], "audit.log")
        evidence["audit_command_status"] = "PASS"
        spec = importlib.util.spec_from_file_location("audit_parser", root / "audit_parser.py")
        assert spec is not None and spec.loader is not None
        audit = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(audit)
        targets = audit.parse_targets(root / "audit-targets.txt")
        source = (root / "ClassicalMechanics/Audit.lean").read_text()
        for pattern in [r"^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$",
                        r"^\s*#check\s+@?([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$"]:
            actual = re.findall(pattern, source, re.MULTILINE)
            if len(actual) != len(targets) or set(actual) != set(targets):
                raise ValueError("Exact named audit signature/axiom target set mismatch.")
        if "sorryAx" in log or re.search(r"declaration uses ['\u2018]sorry|(?:^|\n).*:\s*error:", log):
            raise ValueError("Admission or compiler error in audit.")
        records = audit.parse_axioms(log)
        theorems = []
        for target in targets:
            values = records.get(target, [])
            if len(values) != 1:
                raise ValueError(f"Expected exactly one fresh axiom record: {target}")
            axioms = sorted(audit.normalize_axiom_name(name) for name in values[0])
            if set(axioms) - audit.ALLOWED_AXIOMS:
                raise ValueError(f"Unapproved axiom: {target}: {axioms}")
            theorems.append({"name": target, "axioms": axioms, "status": "PASS_STANDARD_ONLY"})
        verify_sources()
        evidence["theorem_axiom_audit_status"] = "PASS_STANDARD_ONLY"
        evidence["status"] = "PASS"
        save("audit-summary.json", {**evidence, "theorems": theorems,
             "exact_root_promotion": "REQUIRES_SEPARATE_SCOPE_AND_PREMISE_REVIEW"})
        print("EXTERNAL_WINDOWS_COMPILER=PASS; THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        evidence["status"] = "FAIL"
        evidence["failure"] = str(error)
        print(f"EXTERNAL_WINDOWS_VALIDATION=FAIL: {error}", file=sys.stderr)
        return 1
    finally:
        save("run-provenance.json", evidence)


if __name__ == "__main__":
    raise SystemExit(main())
