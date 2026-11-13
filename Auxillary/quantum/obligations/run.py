#!/usr/bin/env python3
"""External cached P1--P7 implementation builds and exact theorem-level axiom audits."""
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
HERE = "Auxillary/quantum/obligations"
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")

def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()

def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[3])
    p.add_argument("--report-directory", type=Path, default=Path("artifacts/external-linux/quantum-obligations"))
    p.add_argument("--dependency-report", type=Path, default=Path("artifacts/external-linux/dependency-preparation.json"))
    p.add_argument("--source-commit", default=os.environ.get("GITHUB_SHA", ""))
    p.add_argument("--expected-platform", choices=("linux", "windows"), default="linux")
    args = p.parse_args()
    root = args.repo_root.resolve()
    report = args.report_directory if args.report_directory.is_absolute() else root / args.report_directory
    report.mkdir(parents=True, exist_ok=True)
    prov = {
        "schema_version": 1, "scope": "quantum_obligation_implementation", "started_at_utc": now(),
        "source_commit": args.source_commit, "requested_toolchain": TOOLCHAIN,
        "requested_mathlib_commit": MATHLIB, "external_platform": platform.system().lower(),
        "stage": "PREPARATION", "commands": [], "module_results": [],
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
        "build_strategy": "INCREMENTAL_MODULE_BUILDS_SKIP_KNOWN_FAILED_DEPENDENCIES",
    }
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, MATHLIB_NO_CACHE_ON_UPDATE="1")
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    errors, results, declaration_results = [], [], []

    def save():
        write_json(report / "provenance.json", prov)
        write_json(report / "module-status.json", {"schema_version": 1, "source_commit": prov["source_commit"], "modules": results})

    def file(relative):
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError(f"Invalid or missing source: {relative}")
        return path

    def run(argv, log):
        start = time.monotonic()
        print("+ " + " ".join(argv), flush=True)
        r = subprocess.run(argv, cwd=root, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
        (report / log).write_text(r.stdout, encoding="utf-8")
        print(r.stdout, end="" if r.stdout.endswith("\n") else "\n", flush=True)
        prov["commands"].append({"argv": argv, "exit_code": r.returncode, "log": log,
                                 "elapsed_seconds": round(time.monotonic() - start, 3)})
        save()
        return r.returncode, r.stdout

    def require_command(argv, log):
        code, output = run(argv, log)
        if code:
            raise RuntimeError(f"Preparation command failed ({code}): {argv!r}")
        return output.strip()

    try:
        save()
        if platform.system().lower() != args.expected_platform:
            raise RuntimeError("EXTERNAL_NATIVE_" + args.expected_platform.upper() + "_REQUIRED")
        if os.environ.get("GITHUB_ACTIONS") != "true" and os.environ.get("NSE_QUANTUM_OBLIGATIONS_EXTERNAL_NATIVE") != "1":
            raise RuntimeError("External opt-in required: NSE_QUANTUM_OBLIGATIONS_EXTERNAL_NATIVE=1")
        if file("lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
            raise RuntimeError("Committed compiler pin differs.")
        head = require_command(["git", "rev-parse", "HEAD"], "source-commit.log")
        if args.source_commit and args.source_commit != head:
            raise RuntimeError("Requested and checked-out source commits differ.")
        prov["source_commit"] = head
        version = require_command(["lean", "--version"], "lean-version.txt")
        if not re.search(r"version 4\.34\.0-rc1,\s*[^,\s]*-" + args.expected_platform + "-", version):
            raise RuntimeError("Matching native " + args.expected_platform + " compiler required.")
        prov["actual_lean_version"] = version
        prep_path = args.dependency_report if args.dependency_report.is_absolute() else root / args.dependency_report
        prep = json.loads(prep_path.read_text(encoding="utf-8"))
        targets = sorted(prep.get("cache_targets", []))
        if not targets or any(not re.fullmatch(r"Mathlib(?:\.[A-Za-z0-9_]+)*", t) for t in targets):
            raise RuntimeError("Verified Mathlib cache targets required.")
        dep_inputs = ["platform=" + args.expected_platform, "toolchain=" + TOOLCHAIN, "compiler=" + version]
        dep_inputs += [n + "=" + sha256(file(n)) for n in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")]
        dep_inputs.append("targets=" + ",".join(targets))
        fingerprint = hashlib.sha256("\n".join(dep_inputs).encode()).hexdigest()
        if prep.get("status") != "PASS" or prep.get("external_platform") != args.expected_platform or prep.get("dependency_fingerprint") != fingerprint:
            raise RuntimeError("Dependency preparation does not match current pins/compiler/configuration.")
        lock = json.loads(file("lake-manifest.json").read_text(encoding="utf-8"))
        expected_deps = {x["name"]: x["rev"] for x in lock["packages"]}
        prepared_deps = {x["name"]: x["revision"] for x in prep["dependency_revisions"]}
        if expected_deps != prepared_deps or expected_deps.get("mathlib") != MATHLIB:
            raise RuntimeError("Prepared dependency commits differ from the lockfile.")
        for name, revision in sorted(expected_deps.items()):
            actual = require_command(["git", "-C", ".lake/packages/" + name, "rev-parse", "HEAD"], "dependency-" + name + ".log")
            if actual != revision:
                raise RuntimeError(f"Actual dependency commit differs: {name}")
        prov["actual_mathlib_commit"] = MATHLIB
        prov["dependency_revisions"] = prepared_deps
        prov["dependency_preparation_sha256"] = sha256(prep_path)
        prov["dependency_fingerprint"] = fingerprint
        prov["dependency_cache_mode"] = "REUSE_VERIFIED_DEPENDENCY_PREPARATION_ONLY"

        spec = importlib.util.spec_from_file_location("axiom_verifier", file("Auxillary/scripts/verify_audit.py"))
        if spec is None or spec.loader is None:
            raise RuntimeError("Exact inherited axiom parser unavailable.")
        verifier = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verifier)
        audit_targets = verifier.parse_targets(file(HERE + "/audit-targets.txt"))
        modules = json.loads(file(HERE + "/module-targets.json").read_text(encoding="utf-8"))
        flat, seen = [], set()
        if not isinstance(modules, list) or not modules:
            raise ValueError("Nonempty explicit module targets required.")
        for item in modules:
            name, path, decls = item["module"], item["path"], item["audit_targets"]
            if not NAME.fullmatch(name) or not (name == "QuantumAdapter.Obligations" or name.startswith("QuantumAdapter.Obligations.")):
                raise ValueError(f"Invalid obligations module: {name}")
            if name in seen or path != "Quantum_adapter/" + name.replace(".", "/") + ".lean":
                raise ValueError(f"Duplicate module or inconsistent source path: {name}")
            if not isinstance(decls, list) or not decls or any(not NAME.fullmatch(d) for d in decls):
                raise ValueError(f"Nonempty explicit audit declarations required: {name}")
            file(path)
            seen.add(name)
            flat.extend(decls)
        if flat != audit_targets or len(flat) != len(set(flat)):
            raise ValueError("module-targets.json and audit-targets.txt must have the same exact ordered unique declarations.")
        scope = json.loads(file(HERE + "/formalization-status.json").read_text(encoding="utf-8"))
        if args.expected_platform == "windows":
            header_spec = importlib.util.spec_from_file_location("native_source_headers",
                file("Fefferman_adapter/scripts/verify_native_sources.py"))
            if header_spec is None or header_spec.loader is None:
                raise RuntimeError("Native source import parser unavailable")
            header_parser = importlib.util.module_from_spec(header_spec)
            header_spec.loader.exec_module(header_parser)
            roots = {"QuantumAdapter": "Quantum_adapter", "NSEQuantumBridge": "Quantum_adapter",
                     "NSEMaxwell": "Fefferman_adapter", "MethlibEndpoints": "Fefferman_adapter",
                     "SingularClosure": "Fefferman_adapter/NativeSources/methlib",
                     "MaxwellEndpoint": "Maxwell_Endpoint"}
            forbidden = {"NSEQuantumForward", "NSEQuantumReverse", "NSEMaxwellForward", "NSEMaxwellReverse"}
            pending, checked = list(seen), set()
            while pending:
                module = pending.pop()
                if module in checked:
                    continue
                checked.add(module)
                prefix = module.split(".")[0]
                if prefix in forbidden:
                    raise RuntimeError("Selected source closure requires a Linux-only arrow path: " + module)
                if prefix in roots:
                    source = file(roots[prefix] + "/" + module.replace(".", "/") + ".lean")
                    pending.extend(header_parser.lean_imports(source.read_text(encoding="utf-8")))
            prov["windows_project_import_closure"] = sorted(checked)

        # One Git inventory; verify every project proof input against its exact committed blob.
        inventory = subprocess.check_output(["git", "ls-tree", "-rz", "--full-tree", head], cwd=root)
        blobs = {}
        for row in inventory.split(b"\0"):
            if row:
                header, name = row.split(b"\t", 1)
                mode, kind, blob = header.decode().split()
                if kind == "blob":
                    blobs[name.decode()] = blob
        inputs = {"lean-toolchain", "lakefile.lean", "lake-manifest.json", "Auxillary/cache-targets.txt", "Auxillary/scripts/verify_audit.py"}
        for relative in blobs:
            if relative.startswith((".github/workflows/", "Auxillary/scripts/", HERE + "/")) or relative in {"Auxillary/run.sh", "Auxillary/run.ps1"}:
                inputs.add(relative)
            if relative.endswith(".lean") and relative.startswith(("Quantum_adapter/", "Fefferman_adapter/", "Maxwell_Endpoint/", "B <-> Quantum/", "B <-> Maxwell/")):
                if "/NativeSources/" not in relative or "/NativeSources/methlib/" in relative:
                    inputs.add(relative)
        inputs.update(item["path"] for item in modules)
        manifest = {"schema_version": 1, "source_commit": head,
                    "scope": "ALL_TRACKED_PROJECT_PROOFS_PLUS_CONFIG; VENDORED_DEPENDENCIES_VERIFIED_BY_PREPARATION_AND_LOCK", "files": []}
        for relative in sorted(inputs):
            # Native Windows uses a sparse checkout: literal arrow paths cannot
            # be materialized. They are not imported by the obligation chain.
            # Preserve their exact Git identity; any attempted Lake import still
            # fails rather than substituting a source or an object file.
            git_only = (args.expected_platform == "windows" and
                        relative.startswith(("B <-> Maxwell/", "B <-> Quantum/")))
            if git_only:
                raw = subprocess.check_output(["git", "cat-file", "blob", blobs[relative]], cwd=root)
            else:
                raw = file(relative).read_bytes()
            actual = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
            expected = blobs.get(relative)
            normalization = "IDENTITY"
            canonical = actual
            # The tracked .gitattributes explicitly checks out *.cmd as CRLF.
            # Only this launcher presentation conversion is accepted; Lean and
            # all other proof inputs still require exact committed bytes.
            if actual != expected and relative.endswith(".cmd"):
                normalized = raw.replace(b"\r\n", b"\n")
                canonical = hashlib.sha1(f"blob {len(normalized)}\0".encode() + normalized).hexdigest()
                normalization = "CMD_CRLF_TO_LF"
            if expected != canonical:
                raise RuntimeError(f"Workspace bytes differ from source commit: {relative}")
            manifest["files"].append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest(),
                "git_blob_sha": canonical, "working_tree_blob_sha": actual,
                "checkout_normalization": normalization,
                "materialization": "GIT_ONLY_WINDOWS_INVALID_PATH" if git_only else "WORKTREE"})
        write_json(report / "source-manifest.json", manifest)
        prov["source_manifest_sha256"] = sha256(report / "source-manifest.json")
        prov["stage"] = "BUILD_AND_AUDIT"

        module_names = {item["module"] for item in modules}
        dependencies = {}
        for item in modules:
            imported = set()
            for line in file(item["path"]).read_text(encoding="utf-8").splitlines():
                if line.startswith("import "):
                    imported.update(line.split("--", 1)[0].split()[1:])
            dependencies[item["module"]] = imported & module_names
        def ancestors(name, visited=None):
            visited = set() if visited is None else visited
            for dependency in dependencies[name]:
                if dependency not in visited:
                    visited.add(dependency)
                    ancestors(dependency, visited)
            return visited
        failed_builds = set()

        for item in modules:
            name, decls = item["module"], item["audit_targets"]
            stem = name.replace(".", "-")
            result = {"module": name, "path": item["path"], "build_status": "NOT_RUN", "audit_status": "NOT_RUN", "audit_targets": decls}
            results.append(result)
            prov["module_results"] = results
            save()
            blocked = sorted(ancestors(name) & failed_builds)
            if blocked:
                result["build_status"] = "BLOCKED_BY_FAILED_DEPENDENCY"
                result["audit_status"] = "SKIPPED_DEPENDENCY_FAILURE"
                result["failed_dependencies"] = blocked
                failed_builds.add(name)
                errors.append(f"{name}: blocked by failed dependencies {blocked}")
                declaration_results.extend({"name": d, "module": name,
                    "status": "SKIPPED_DEPENDENCY_FAILURE"} for d in decls)
                print(f"BLOCKED {name}: {', '.join(blocked)}", flush=True)
                save()
                continue
            code, _ = run(["lake", "build", "--no-build", name], "freshness-" + stem + ".log")
            result["freshness_exit_code"] = code
            if code == 3:
                code, _ = run(["lake", "build", name], "build-" + stem + ".log")
            result["build_exit_code"] = code
            result["build_status"] = "PASS" if code == 0 else "FAIL"
            if code:
                failed_builds.add(name)
                result["audit_status"] = "SKIPPED_BUILD_FAILURE"
                errors.append(f"{name}: build failed ({code})")
                declaration_results.extend({"name": d, "module": name, "status": "SKIPPED_BUILD_FAILURE"} for d in decls)
                save()
                continue
            audit = "import " + name + "\nset_option pp.universes true\nset_option pp.fullNames true\n"
            audit += "".join(f"#check @{d}\n#print axioms {d}\n" for d in decls)
            audit_path = report / (stem + "-Audit.lean")
            audit_path.write_text(audit, encoding="utf-8")
            result["audit_source_sha256"] = sha256(audit_path)
            code, output = run(["lake", "env", "lean", str(audit_path)], "audit-" + stem + ".log")
            result["audit_exit_code"] = code
            module_errors = []
            if code or "sorryAx" in output or re.search(r"(?:^|\n).*:\s*error:", output):
                module_errors.append("Fresh audit compiler failure or admission.")
            try:
                records = verifier.parse_axioms(output)
                if set(records) != set(decls):
                    module_errors.append("Fresh axiom record names differ from the explicit targets.")
                for declaration in decls:
                    rows = records.get(declaration, [])
                    if len(rows) != 1:
                        module_errors.append(f"{declaration}: expected one record, found {len(rows)}")
                        declaration_results.append({"name": declaration, "module": name, "status": "MISSING_OR_DUPLICATE"})
                        continue
                    axioms = sorted({verifier.normalize_axiom_name(a) for a in rows[0]})
                    bad = sorted(set(axioms) - verifier.ALLOWED_AXIOMS)
                    if bad:
                        module_errors.append(f"{declaration}: unapproved axioms {bad}")
                    declaration_results.append({"name": declaration, "module": name,
                        "status": "PASS_STANDARD_ONLY" if not bad and not code else "FAIL", "axioms": axioms, "unapproved_axioms": bad})
            except Exception as error:
                module_errors.append(f"Axiom parser rejected output: {error}")
            result["audit_status"] = "FAIL" if module_errors else "PASS_STANDARD_ONLY"
            result["errors"] = module_errors
            errors.extend(f"{name}: {e}" for e in module_errors)
            save()

        for item in manifest["files"]:
            if item.get("materialization") == "GIT_ONLY_WINDOWS_INVALID_PATH":
                continue
            if sha256(file(item["path"])) != item["sha256"]:
                errors.append("Source changed during external run: " + item["path"])
        status = "FAIL" if errors else "PASS_STANDARD_ONLY"
        summary = {"schema_version": 1, "status": status, "source_commit": head,
            "compiler": version, "mathlib_commit": MATHLIB,
            "source_manifest_sha256": sha256(report / "source-manifest.json"),
            "module_count": len(modules), "theorem_count": len(audit_targets), "modules": results,
            "root_module_included": "QuantumAdapter.Obligations" in seen,
            "obligation_discharge": "REQUIRES_EXACT_SIGNATURE_SCOPE_REVIEW",
            "theorems": declaration_results, "declared_formalization_scope": scope, "errors": errors,
            "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT", "exact_root_promotion": "REQUIRES_SCOPE_AND_PREMISE_REVIEW"}
        write_json(report / "audit-summary.json", summary)
        prov["stage"], prov["theorem_axiom_audit_status"], prov["completed_at_utc"] = "COMPLETE", status, now()
        save()
        print(f"QUANTUM_OBLIGATIONS_AXIOM_AUDIT={status}; modules={len(modules)}; declarations={len(audit_targets)}", flush=True)
        return 1 if errors else 0
    except Exception as error:
        prov["stage"], prov["failure"], prov["completed_at_utc"] = "FAILED", f"{type(error).__name__}: {error}", now()
        save()
        write_json(report / "audit-summary.json", {"schema_version": 1, "status": "FAIL", "source_commit": prov["source_commit"],
            "modules": results, "theorems": declaration_results, "errors": [*errors, prov["failure"]],
            "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"})
        print(prov["failure"], file=sys.stderr)
        return 1

if __name__ == "__main__":
    raise SystemExit(main())
