#!/usr/bin/env python3
"""External native GR assembly and sequential named endpoint audits; caches preserved.

Invoke only on an external native compiler / GitHub Actions. Python syntax or
manifest checks in an authoring environment do not execute Lean.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
COMPILER_COMMIT = "3447a668783dbce1a8fdb97101dd067687b2b418"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
SOURCE_NAME = re.compile(r"[\w']+(?:\.[\w']+)*\Z", re.UNICODE)
RECORD = re.compile(r"['‘](?P<name>[^'’\r\n]+)['’]\s+"
                    r"(?:does not depend on any axioms|depends on axioms:\s*"
                    r"\[(?P<axioms>[^\]]*)\])", re.MULTILINE)
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def audit_records(log: str, targets: list[str]) -> list[dict]:
    text = ANSI.sub("", log)
    require("sorryAx" not in text, "sorryAx in endpoint audit")
    require(not re.search(r"declaration uses ['‘]sorry", text), "sorry declaration")
    require(not re.search(r"(?:^|\n).*:\s*error:", text), "Lean error in audit output")
    records: dict[str, list[set[str]]] = {}
    for match in RECORD.finditer(text):
        axioms = set(filter(None, (x.strip() for x in (match.group("axioms") or "").split(","))))
        records.setdefault(match.group("name"), []).append(axioms)
    result = []
    for name in targets:
        found = records.get(name, [])
        require(len(found) == 1, f"Expected one named audit for {name}; got {len(found)}")
        require(not found[0] - ALLOWED, f"Unapproved axioms for {name}: {sorted(found[0] - ALLOWED)}")
        result.append({"name": name, "status": "PASS_STANDARD_ONLY", "axioms": sorted(found[0])})
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, required=True)
    parser.add_argument("--expected-platform", choices=("linux", "windows"), required=True)
    parser.add_argument("--phase", choices=("all", "dependencies", "build"), default="all")
    parser.add_argument("--report-directory", type=Path)
    parser.add_argument("--source-commit", default=os.environ.get("GITHUB_SHA", ""))
    parser.add_argument("--module", action="append", help="Select new assembly modules; baseline GR and TEMP stages still run")
    args = parser.parse_args()
    package = args.package_root.resolve()
    repo = package.parent
    support = repo / "Auxillary" / "GR" / "Assembly"
    report = (args.report_directory or support / "evidence-current").resolve()
    report.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["ELAN_TOOLCHAIN"] = TOOLCHAIN
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env.setdefault("LEAN_NUM_THREADS", "4")
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    provenance = {
        "schema_version": 1, "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "source_commit": args.source_commit, "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "requested_toolchain": TOOLCHAIN, "requested_compiler_commit": COMPILER_COMMIT,
        "requested_mathlib_commit": MATHLIB, "external_platform": platform.system().lower(),
        "phase": args.phase, "cache_policy": "PRESERVE_AND_REUSE_COMPATIBLE_OBJECTS",
        "commands": [], "stages": [], "status": "RUNNING",
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
        "root_promotion": "REQUIRES_EXACT_ROOT_TYPE_AND_PREMISE_REVIEW",
    }

    def persist():
        write_json(report / ("provenance-" + args.phase + ".json"), provenance)

    def run(command, log_name, cwd=package):
        output = []
        started = time.monotonic()
        print("COMMAND=" + " ".join(command), flush=True)
        with (report / log_name).open("w", encoding="utf-8") as log:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
            assert process.stdout is not None
            for line in process.stdout:
                log.write(line)
                log.flush()
                output.append(line)
                print(line, end="", flush=True)
            exit_code = process.wait()
        provenance["commands"].append({"command": command, "log": log_name,
            "exit_code": exit_code, "seconds": round(time.monotonic() - started, 3)})
        persist()
        require(exit_code == 0, f"Command failed ({exit_code}): {command}; log={log_name}")
        return "".join(output)

    def verify_dependencies(lock):
        result = []
        for entry in lock["packages"]:
            require(entry["type"] == "git" and re.fullmatch(r"[a-f0-9]{40}", entry["rev"]),
                    "Every dependency must be an immutable Git revision")
            name = entry["name"]
            require(re.fullmatch(r"[A-Za-z0-9_-]+", name), "Invalid dependency name")
            checkout = package / ".lake" / "packages" / name
            revision = run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                           f"dependency-{name}-revision.log").strip()
            require(revision == entry["rev"], "Dependency revision mismatch: " + name)
            status = run(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"],
                         f"dependency-{name}-working-tree.log")
            require(not status.strip(), "Tracked dependency modification: " + name)
            result.append({"name": name, "revision": revision})
        return result

    persist()
    try:
        require(platform.system().lower() == args.expected_platform, "Native compiler platform mismatch")
        require((package / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain file mismatch")
        lock_path = package / "lake-manifest.json"
        lock_hash = digest(lock_path)
        lock = json.loads(lock_path.read_text())
        mathlib = [entry for entry in lock["packages"] if entry["name"] == "mathlib"]
        require(len(mathlib) == 1 and mathlib[0]["rev"] == MATHLIB, "Mathlib lock mismatch")
        version = run(["lean", "--version"], "lean-version-" + args.phase + ".log")
        require(re.search(r"version 4\.34\.0-rc1,\s*[^,\s]*-" + args.expected_platform + r"-[^,\s]*,", version),
                "Actual native compiler version/target mismatch")
        require(COMPILER_COMMIT[:7] in version, "Compiler commit mismatch")
        provenance["actual_lean_version"] = version.strip()
        if args.phase in {"all", "dependencies"}:
            run(["lake", "env", "lean", "--version"], "dependency-resolution.log")
            require(digest(lock_path) == lock_hash, "Dependency resolution changed committed lock")
            provenance["dependency_revisions"] = verify_dependencies(lock)
            run(["lake", "exe", "cache", "get", "Mathlib"], "mathlib-cache-get.log")
            require(digest(lock_path) == lock_hash, "Cache acquisition changed committed lock")
            provenance["dependency_status"] = "PASS"
            persist()
        if args.phase == "dependencies":
            provenance["status"] = "PASS"
            persist()
            return 0

        provenance["dependency_revisions"] = verify_dependencies(lock)
        provenance["actual_mathlib_commit"] = MATHLIB
        baseline = json.loads((repo / "Auxillary/GR/audit-targets.json").read_text())
        require(set(baseline) == {"adapter", "forward", "reverse"}, "Wrong baseline stage inventory")
        require(sum(len(v) for v in baseline.values()) == 401, "Expected the frozen 401 baseline GR audits")
        cutouts = json.loads((repo / "Auxillary/TEMP/audit-targets.json").read_text())
        require(isinstance(cutouts, list) and len(cutouts) == 85, "Expected the frozen 85 cutout endpoint audits")
        require(len({x["name"] for x in cutouts}) == len(cutouts), "Duplicate cutout target")
        require(all(SOURCE_NAME.fullmatch(x["name"]) and NAME.fullmatch(x["module"]) for x in cutouts),
                "Invalid cutout declaration/module name")
        cutout_imports = set(re.findall(r"^import\s+(\S+)\s*$",
            (repo / "TEMP/TempEndpoints.lean").read_text(), re.MULTILINE))
        require({x["module"] for x in cutouts} <= cutout_imports,
                "TempEndpoints is missing selected cutout imports")
        inventory = json.loads((support / "audit-targets.json").read_text())
        require(isinstance(inventory, list) and bool(inventory), "New assembly audit inventory must be nonempty")
        require(len({x["name"] for x in inventory}) == len(inventory), "Duplicate new assembly target")
        require(all(SOURCE_NAME.fullmatch(x["name"]) and NAME.fullmatch(x["module"]) for x in inventory),
                "Invalid new assembly declaration/module name")
        require(all(x["module"].startswith("GRAssembly") for x in inventory), "Unexpected assembly module prefix")
        all_baseline = {name for values in baseline.values() for name in values}
        require(not all_baseline.intersection(x["name"] for x in inventory), "New target duplicates baseline declaration")
        cutout_names = {x["name"] for x in cutouts}
        require(not all_baseline.intersection(cutout_names), "Cutout target duplicates baseline declaration")
        require(not cutout_names.intersection(x["name"] for x in inventory), "New target duplicates cutout declaration")
        selected = inventory
        if args.module:
            requested = set(args.module)
            require(requested <= {x["module"] for x in inventory}, "Unknown selected assembly module")
            selected = [x for x in inventory if x["module"] in requested]
        scope = json.loads((support / "formalization-status.json").read_text())
        scope.update({"selected_modules": sorted({x["module"] for x in selected}),
                      "selected_new_target_count": len(selected), "full_new_target_count": len(inventory),
                      "baseline_target_count": 401, "cutout_target_count": len(cutouts),
                      "cutout_validation": "FRESH_NAMED_AXIOM_AUDITS; SOURCE_TYPE_EQUALITY_RETAINS_PRIOR_CERTIFICATE",
                      "selection_mode": "selected_modules" if args.module else "full"})
        write_json(report / "declared-scope.json", scope)
        inputs = set()
        for source_root in [package, repo / "GR_adapter", repo / "TEMP"]:
            require(source_root.is_dir(), "Missing source directory: " + str(source_root))
            for suffix in ("*.lean", "*.json"):
                inputs.update(p for p in source_root.rglob(suffix)
                              if ".lake" not in p.parts and "__pycache__" not in p.parts)
            inputs.add(source_root / "lean-toolchain")
        inputs.update([package / "run.cmd", package / "run.sh", Path(__file__).resolve(),
                       support / "audit-targets.json", support / "formalization-status.json",
                       repo / "Auxillary/GR/audit-targets.json", repo / "Auxillary/TEMP/audit-targets.json"])
        manifest = {"source_commit": args.source_commit,
                    "source_roots": ["ASSEMBLY", "GR_adapter", "TEMP"],
                    "files": [{"path": p.relative_to(repo).as_posix(), "sha256": digest(p)} for p in sorted(inputs)]}
        write_json(report / "source-manifest.json", manifest)
        provenance["source_manifest_sha256"] = digest(report / "source-manifest.json")
        stages = [("adapter", "GRAdapter", baseline["adapter"]),
                  ("forward", "NSEGRForward", baseline["forward"]),
                  ("reverse", "NSEGRReverse", baseline["reverse"]),
                  ("cutouts", "TempEndpoints", [x["name"] for x in cutouts])]
        if args.module:
            for number, module in enumerate(sorted({x["module"] for x in selected}), 1):
                stages.append((f"assembly-{number:03d}", module,
                               [x["name"] for x in selected if x["module"] == module]))
        else:
            stages.append(("assembly", "GRAssembly", [x["name"] for x in selected]))
        stage_summaries = []
        for stage, module, names in stages:
            require(bool(names), "Empty named stage: " + stage)
            require(len(set(names)) == len(names) and all(SOURCE_NAME.fullmatch(n) for n in names),
                    "Invalid named stage: " + stage)
            run(["lake", "build", module], stage + "-build.log")
            audit = report / (stage.replace("-", "_").title() + "Audit.lean")
            text = "import " + module + "\nset_option pp.universes false\n"
            text += "\n".join("#check @" + name + "\n#print axioms " + name for name in names) + "\n"
            audit.write_text(text, encoding="utf-8")
            log_name = stage + "-audit.log"
            log = run(["lake", "env", "lean", "-R", str(report), str(audit)], log_name)
            records = audit_records(log, names)
            entry = {"stage": stage, "module": module, "status": "PASS_STANDARD_ONLY",
                     "source_commit": args.source_commit, "target_count": len(records),
                     "audit_source": audit.name, "audit_source_sha256": digest(audit),
                     "audit_log": log_name, "audit_log_sha256": digest(report / log_name), "targets": records}
            write_json(report / (stage + "-summary.json"), entry)
            stage_summaries.append(entry)
            provenance["stages"] = stage_summaries
            persist()
        require(digest(lock_path) == lock_hash, "Compilation changed committed dependency lock")
        for item in manifest["files"]:
            require(digest(repo / item["path"]) == item["sha256"], "Source changed during run: " + item["path"])
        summary = {"schema_version": 1, "status": "PASS_STANDARD_ONLY", "source_commit": args.source_commit,
                   "actual_lean_version": version.strip(), "actual_mathlib_commit": MATHLIB,
                   "source_manifest_sha256": provenance["source_manifest_sha256"], "source_input_verification": "PASS",
                   "baseline_target_count": 401, "cutout_target_count": len(cutouts),
                   "new_target_count": len(selected),
                   "target_count": sum(x["target_count"] for x in stage_summaries),
                   "allowed_axioms": sorted(ALLOWED), "stages": stage_summaries, "declared_scope": scope,
                   "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"}
        write_json(report / "audit-summary.json", summary)
        provenance["status"] = "PASS_STANDARD_ONLY"
        persist()
        print(f"BASELINE_GR_AUDITS=401; CUTOUT_AUDITS={len(cutouts)}; "
              f"NEW_ASSEMBLY_AUDITS={len(selected)}; STATUS=PASS_STANDARD_ONLY", flush=True)
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        provenance["status"] = "FAIL"
        provenance["error"] = str(error)
        persist()
        print("GR_ASSEMBLY_EXTERNAL_ERROR=" + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())


