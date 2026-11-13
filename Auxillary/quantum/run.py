#!/usr/bin/env python3
"""External-only cached Quantum adapter compilation and fresh named axiom audit."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
STAGES = {"adapter": 0, "forward": 1, "reverse": 2, "assembly": 3}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")

def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    p.add_argument("--report-directory", type=Path, default=Path("artifacts/external-linux/quantum"))
    p.add_argument("--source-commit", default=os.environ.get("GITHUB_SHA", ""))
    args = p.parse_args()
    root = args.repo_root.resolve()
    report = args.report_directory if args.report_directory.is_absolute() else root / args.report_directory
    report.mkdir(parents=True, exist_ok=True)
    prov = {
        "schema_version": 1, "scope": "quantum_adapter_and_ordered_implications",
        "started_at_utc": now(), "requested_toolchain": TOOLCHAIN,
        "requested_mathlib_commit": MATHLIB, "external_platform": platform.system().lower(),
        "source_commit": args.source_commit, "build_status": "NOT_RUN",
        "audit_command_status": "NOT_RUN", "theorem_axiom_audit_status": "NOT_RUN",
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT", "commands": [],
    }
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, MATHLIB_NO_CACHE_ON_UPDATE="1")
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)

    def save():
        write_json(report / "provenance.json", prov)

    def run(argv, log, allowed=(0,)):
        started = time.monotonic()
        print("+ " + " ".join(argv), flush=True)
        r = subprocess.run(argv, cwd=root, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
        (report / log).write_text(r.stdout, encoding="utf-8")
        print(r.stdout, end="" if r.stdout.endswith("\n") else "\n", flush=True)
        prov["commands"].append({"argv": argv, "exit_code": r.returncode, "log": log,
                                 "elapsed_seconds": round(time.monotonic() - started, 3)})
        save()
        if r.returncode not in allowed:
            raise RuntimeError(f"External command failed ({r.returncode}): {argv!r}")
        return r.returncode, r.stdout

    def file(relative):
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError(f"Invalid source: {relative}")
        return path

    try:
        save()
        if platform.system() != "Linux":
            raise RuntimeError("EXTERNAL_NATIVE_LINUX_REQUIRED")
        if os.environ.get("GITHUB_ACTIONS") != "true" and os.environ.get("NSE_QUANTUM_EXTERNAL_NATIVE") != "1":
            raise RuntimeError("External opt-in required: NSE_QUANTUM_EXTERNAL_NATIVE=1")
        if file("lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise RuntimeError("Committed compiler pin differs.")
        _, head = run(["git", "rev-parse", "HEAD"], "source-commit.log")
        head = head.strip()
        if args.source_commit and args.source_commit != head:
            raise RuntimeError("Requested and checked-out source commits differ.")
        prov["source_commit"] = head
        _, version = run(["lean", "--version"], "lean-version.txt")
        prov["actual_lean_version"] = version.strip()
        if not re.search(r"version 4\.34\.0-rc1,\s*[^,\s]*-linux-", version):
            raise RuntimeError("Matching native Linux compiler required.")
        _, mathlib = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], "mathlib-revision.txt")
        prov["actual_mathlib_commit"] = mathlib.strip()
        if mathlib.strip() != MATHLIB:
            raise RuntimeError("Actual Mathlib revision differs.")
        inherited = root / "artifacts/external-linux"
        prep = json.loads((inherited / "dependency-preparation.json").read_text())
        prior = json.loads((inherited / "audit-summary.json").read_text())
        prior_manifest = json.loads((inherited / "source-manifest.json").read_text())
        if prep.get("status") != "PASS":
            raise RuntimeError("Verified cached dependency preparation required.")
        if prior.get("status") != "PASS_STANDARD_ONLY" or prior.get("source_commit") != head:
            raise RuntimeError("Fresh matching integrated root audit required.")
        for item in prior_manifest["files"]:
            if sha256(file(item["path"])) != item["sha256"].lower():
                raise RuntimeError(f"Inherited proof input changed: {item['path']}")
        prov["dependency_cache_mode"] = "REUSE_VERIFIED_REPOSITORY_DEPENDENCY_PHASE"
        prov["inherited_root_evidence"] = {n: sha256(inherited / n) for n in
            ("dependency-preparation.json", "source-manifest.json", "audit-summary.json")}

        modules = json.loads(file("Auxillary/quantum/module-order.json").read_text())
        if not isinstance(modules, list) or not modules:
            raise ValueError("Explicit nonempty module schedule required.")
        names, order = [], []
        for item in modules:
            name, path, stage = item["module"], item["path"], item["stage"]
            if not MODULE.fullmatch(name) or stage not in STAGES or not path.endswith(".lean"):
                raise ValueError(f"Malformed module schedule item: {item}")
            file(path)
            names.append(name)
            order.append(STAGES[stage])
        if len(names) != len(set(names)) or order != sorted(order):
            raise ValueError("Require unique adapter -> forward -> reverse -> assembly order.")
        prov["module_schedule"] = modules

        spec = importlib.util.spec_from_file_location("axiom_verifier", file("Auxillary/scripts/verify_audit.py"))
        if spec is None or spec.loader is None:
            raise RuntimeError("Inherited exact axiom parser unavailable.")
        verifier = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verifier)
        targets = verifier.parse_targets(file("Auxillary/quantum/audit-targets.txt"))
        scope = json.loads(file("Auxillary/quantum/formalization-status.json").read_text())

        inputs = {item["path"] for item in modules}
        for rel in ("Quantum_adapter", "B <-> Quantum"):
            directory = root / rel
            if directory.is_dir():
                inputs.update(x.relative_to(root).as_posix() for x in directory.rglob("*.lean") if x.is_file())
        inputs.update(("lean-toolchain", "lakefile.lean", "lake-manifest.json",
            ".github/workflows/lean-linux.yml", "Auxillary/scripts/verify_audit.py",
            "Auxillary/quantum/run.py", "Auxillary/quantum/run.sh",
            "Auxillary/quantum/module-order.json", "Auxillary/quantum/audit-targets.txt",
            "Auxillary/quantum/formalization-status.json"))
        manifest = {"schema_version": 1, "source_commit": head, "files": []}
        for relative in sorted(inputs):
            path = file(relative)
            expected = subprocess.check_output(["git", "rev-parse", f"{head}:{relative}"], cwd=root, text=True).strip()
            raw = path.read_bytes()
            actual = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
            if actual != expected:
                raise RuntimeError(f"Workspace bytes differ from committed input: {relative}")
            manifest["files"].append({"path": relative, "sha256": sha256(path), "git_blob_sha": actual})
        write_json(report / "source-manifest.json", manifest)
        prov["source_manifest_sha256"] = sha256(report / "source-manifest.json")
        save()

        freshness, _ = run(["lake", "build", "--no-build", *names], "run-build-freshness.log", (0, 3))
        prov["freshness_check_exit_code"] = freshness
        prov["executed_module_builds"] = 0
        prov["executed_stage_builds"] = 0
        prov["build_strategy"] = "LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE" if freshness == 0 else "STAGED_INCREMENTAL_REBUILD"
        if freshness == 3:
            for stage in STAGES:
                stage_names = [item["module"] for item in modules if item["stage"] == stage]
                if not stage_names:
                    continue
                prov["current_stage"], prov["current_modules"] = stage, stage_names
                save()
                run(["lake", "build", *stage_names], "build-" + stage + ".log")
                prov["executed_module_builds"] += len(stage_names)
                prov["executed_stage_builds"] += 1
                save()
        prov["build_status"] = "PASS"
        save()

        audit = "\n".join("import " + name for name in names)
        audit += "\n\nset_option pp.universes true\nset_option pp.fullNames true\n\n"
        audit += "".join(f"#check @{name}\n#print axioms {name}\n" for name in targets)
        audit_path = report / "QuantumAudit.lean"
        audit_path.write_text(audit, encoding="utf-8")
        prov["generated_audit_source_sha256"] = sha256(audit_path)
        _, log = run(["lake", "env", "lean", str(audit_path)], "run-audit.log")
        prov["audit_command_status"] = "PASS"
        records, errors, results = verifier.parse_axioms(log), [], []
        if "sorryAx" in log or re.search(r"(?:^|\n).*:\s*error:", log):
            errors.append("Admission or compiler error in fresh audit output.")
        for name in targets:
            found = records.get(name, [])
            if len(found) != 1:
                errors.append(f"{name}: expected one axiom record, found {len(found)}")
                results.append({"name": name, "status": "MISSING_OR_DUPLICATE"})
                continue
            axioms = sorted({verifier.normalize_axiom_name(a) for a in found[0]})
            bad = sorted(set(axioms) - verifier.ALLOWED_AXIOMS)
            if bad:
                errors.append(f"{name}: unapproved axioms {bad}")
            results.append({"name": name, "status": "FAIL" if bad else "PASS_STANDARD_ONLY",
                            "axioms": axioms, "unapproved_axioms": bad})
        for item in manifest["files"]:
            if sha256(file(item["path"])) != item["sha256"]:
                errors.append(f"Source changed during compilation: {item['path']}")
        summary = {
            "schema_version": 1, "status": "FAIL" if errors else "PASS_STANDARD_ONLY",
            "source_commit": head, "source_manifest_sha256": sha256(report / "source-manifest.json"),
            "compiler": version.strip(), "mathlib_commit": mathlib.strip(),
            "theorem_count": len(targets), "theorems": results, "declared_formalization_scope": scope,
            "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
            "exact_root_promotion": "REQUIRES_SCOPE_AND_PREMISE_REVIEW", "errors": errors,
        }
        write_json(report / "audit-summary.json", summary)
        if errors:
            raise RuntimeError("; ".join(errors))
        prov["theorem_axiom_audit_status"], prov["stage"] = "PASS_STANDARD_ONLY", "COMPLETE"
        prov["completed_at_utc"] = now()
        save()
        print(f"QUANTUM_THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY ({len(targets)}/{len(targets)})")
        print("SEMANTIC_DISCHARGE=NOT_INFERRED_FROM_AXIOM_AUDIT")
        return 0
    except Exception as error:
        prov["stage"], prov["failure"], prov["completed_at_utc"] = "FAILED", f"{type(error).__name__}: {error}", now()
        save()
        write_json(report / "audit-summary.json", {
            "schema_version": 1, "status": "FAIL", "source_commit": prov["source_commit"],
            "errors": [prov["failure"]], "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"})
        print(prov["failure"], file=sys.stderr)
        return 1

if __name__ == "__main__":
    raise SystemExit(main())

