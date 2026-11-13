#!/usr/bin/env python3
"""External native TEMP compilation and exact endpoint audits; caches preserved.

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
    parser.add_argument("--entry", action="append", help="Optional entry filter, e.g. ML001 or ME16")
    args = parser.parse_args()
    package = args.package_root.resolve()
    repo = package.parent
    support = repo / "Auxillary" / "TEMP"
    report = (args.report_directory or support / "evidence-current").resolve()
    report.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["ELAN_TOOLCHAIN"] = TOOLCHAIN
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env.setdefault("LEAN_NUM_THREADS", "4")
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    provenance: dict = {
        "schema_version": 1,
        "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "source_commit": args.source_commit,
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "requested_toolchain": TOOLCHAIN,
        "requested_compiler_commit": COMPILER_COMMIT,
        "requested_mathlib_commit": MATHLIB,
        "external_platform": platform.system().lower(),
        "phase": args.phase,
        "cache_policy": "PRESERVE_AND_REUSE_COMPATIBLE_OBJECTS",
        "commands": [], "status": "RUNNING",
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
        "gr_law_or_root_promotion": "NONE",
    }

    def persist() -> None:
        write_json(report / ("provenance-" + args.phase + ".json"), provenance)

    def run(command: list[str], log_name: str, cwd: Path = package) -> str:
        output: list[str] = []
        started = time.monotonic()
        print("COMMAND=" + " ".join(command), flush=True)
        with (report / log_name).open("w", encoding="utf-8") as log:
            proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
            assert proc.stdout is not None
            for line in proc.stdout:
                log.write(line)
                log.flush()
                output.append(line)
                print(line, end="", flush=True)
            code = proc.wait()
        provenance["commands"].append({"command": command, "log": log_name,
            "exit_code": code, "seconds": round(time.monotonic() - started, 3)})
        persist()
        require(code == 0, f"Command failed ({code}): {command}; log={log_name}")
        return "".join(output)

    def verify_dependencies(manifest: dict) -> list[dict]:
        result = []
        for entry in manifest["packages"]:
            require(entry["type"] == "git" and re.fullmatch(r"[a-f0-9]{40}", entry["rev"]) is not None,
                    "Dependency must be an immutable Git revision")
            name = entry["name"]
            require(re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None, "Invalid dependency name")
            checkout = package / ".lake" / "packages" / name
            revision = run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                           f"dependency-{name}-revision.log").strip()
            require(revision == entry["rev"], f"Dependency revision mismatch: {name}")
            status = run(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"],
                         f"dependency-{name}-working-tree.log")
            require(not status.strip(), f"Tracked dependency modification: {name}")
            result.append({"name": name, "revision": revision})
        return result

    persist()
    try:
        require(platform.system().lower() == args.expected_platform, "Native compiler platform mismatch")
        require((package / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain file mismatch")
        lock = package / "lake-manifest.json"
        lock_hash = digest(lock)
        manifest = json.loads(lock.read_text())
        matches = [p for p in manifest["packages"] if p["name"] == "mathlib"]
        require(len(matches) == 1 and matches[0]["rev"] == MATHLIB, "Mathlib lock mismatch")
        version = run(["lean", "--version"], "lean-version-" + args.phase + ".log")
        require(re.search(r"version 4\.34\.0-rc1,\s*[^,\s]*-" + args.expected_platform + r"-[^,\s]*,", version) is not None,
                "Actual native Lean compiler version/target mismatch")
        require(COMPILER_COMMIT[:7] in version, "Actual compiler commit mismatch")
        provenance["actual_lean_version"] = version.strip()
        if args.phase in {"all", "dependencies"}:
            run(["lake", "env", "lean", "--version"], "dependency-resolution.log")
            require(digest(lock) == lock_hash, "Dependency resolution changed committed lock")
            provenance["dependency_revisions"] = verify_dependencies(manifest)
            run(["lake", "exe", "cache", "get", "Mathlib"], "mathlib-cache-get.log")
            require(digest(lock) == lock_hash, "Cache acquisition changed committed lock")
            provenance["dependency_status"] = "PASS"
            persist()
        if args.phase == "dependencies":
            provenance["status"] = "PASS"
            persist()
            return 0

        provenance["dependency_revisions"] = verify_dependencies(manifest)
        provenance["actual_mathlib_commit"] = MATHLIB
        inventories = json.loads((support / "audit-targets.json").read_text())
        require(len(inventories) == 85, "Expected exactly 85 cutout endpoint exports")
        require(len({x["name"] for x in inventories}) == 85, "Duplicate endpoint exports")
        require(len({x["module"] for x in inventories}) == 85, "Duplicate endpoint modules")
        require(all(NAME.fullmatch(x["name"]) and NAME.fullmatch(x["module"]) for x in inventories),
                "Invalid endpoint/module name")
        selected = inventories
        if args.entry:
            requested = set(args.entry)
            require(requested <= {x["entry"] for x in inventories}, "Unknown --entry")
            selected = [x for x in inventories if x["entry"] in requested]
        require(bool(selected), "No selected endpoints")
        scope = json.loads((support / "formalization-status.json").read_text())
        scope["selected_entries"] = sorted({x["entry"] for x in selected})
        scope["selected_endpoint_count"] = len(selected)
        scope["build_mode"] = "full" if len(selected) == 85 else "selected_entries"
        write_json(report / "declared-scope.json", scope)
        for entry in inventories:
            endpoint_path = package / (entry["module"].replace(".", "/") + ".lean")
            require(endpoint_path.is_file(), "Missing endpoint module " + entry["module"])
            metadata = json.loads(endpoint_path.with_name("source.json").read_text())
            source_name = metadata.get("source_name", metadata.get("upstream_name"))
            exported = metadata.get("export_name", metadata.get("endpoint", metadata.get("export", metadata.get("candidate_export"))))
            require(isinstance(source_name, str) and SOURCE_NAME.fullmatch(source_name), "Missing source declaration name")
            require(exported == entry["name"], "Endpoint export does not match source metadata")
            entry["source_name"] = source_name
        inputs = sorted({p for p in package.rglob("*.lean") if ".lake" not in p.parts}
            | {p for p in package.rglob("*.json") if ".lake" not in p.parts}
            | {package / "lean-toolchain", package / "run.sh", package / "run.cmd",
               Path(__file__).resolve(), support / "audit-targets.json", support / "formalization-status.json"})
        source_manifest = {"source_commit": args.source_commit,
            "files": [{"path": p.relative_to(repo).as_posix(), "sha256": digest(p)} for p in inputs]}
        write_json(report / "source-manifest.json", source_manifest)
        provenance["source_manifest_sha256"] = digest(report / "source-manifest.json")
        targets = ["TempEndpoints"] if len(selected) == 85 else [x["module"] for x in selected]
        provenance["build"] = "RUNNING"
        persist()
        run(["lake", "build", *targets], "endpoints-build.log")
        provenance["build"] = "PASS"
        audit = report / "EndpointAudit.lean"
        source = "\n".join("import " + x["module"] for x in selected)
        source += "\nset_option pp.universes false\nopen Lean Meta Elab Command\n"
        for entry in selected:
            source += "#check @" + entry["name"] + "\n#print axioms " + entry["name"] + "\n"
            source += f'''run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `{entry["name"]}
  let sourceInfo ← Lean.getConstInfo `{entry["source_name"]}
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: {entry["name"]}"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `{entry["name"]}
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `{entry["source_name"]}
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: {entry["name"]}"
  Lean.logInfo "TYPE_MATCH {entry["name"]}"
'''
        audit.write_text(source, encoding="utf-8")
        log = run(["lake", "env", "lean", "-R", str(report), str(audit)], "endpoints-audit.log")
        records = audit_records(log, [x["name"] for x in selected])
        type_matches = re.findall(r"TYPE_MATCH (GRTemp\.[A-Za-z0-9_.]+)", ANSI.sub("", log))
        require(sorted(type_matches) == sorted(x["name"] for x in selected),
                "Expected one exact source-type match for every selected endpoint")
        require(digest(lock) == lock_hash, "Build changed committed lock")
        for item in source_manifest["files"]:
            require(digest(repo / item["path"]) == item["sha256"], "Source changed during run: " + item["path"])
        summary = {"schema_version": 1, "status": "PASS_STANDARD_ONLY", "source_commit": args.source_commit,
            "actual_lean_version": provenance["actual_lean_version"], "actual_mathlib_commit": MATHLIB,
            "source_manifest_sha256": provenance["source_manifest_sha256"], "source_input_verification": "PASS",
            "audit_source_sha256": digest(audit), "audit_log_sha256": digest(report / "endpoints-audit.log"),
            "target_count": len(selected), "allowed_axioms": sorted(ALLOWED), "targets": records,
            "source_type_match": "PASS", "source_type_match_count": len(type_matches),
            "source_type_pairs": [{"export": x["name"], "source": x["source_name"]} for x in selected],
            "declared_scope": scope, "semantic_discharge": "NOT_INFERRED", "gr_law_or_root_promotion": "NONE"}
        write_json(report / "audit-summary.json", summary)
        provenance["status"] = "PASS_STANDARD_ONLY"
        provenance["audit"] = "PASS_STANDARD_ONLY"
        persist()
        print(f"TEMP_ENDPOINTS={len(records)}; BUILD=PASS; NAMED_AXIOM_AUDIT=PASS_STANDARD_ONLY", flush=True)
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        provenance["status"] = "FAIL"
        provenance["error"] = str(error)
        persist()
        print("TEMP_EXTERNAL_ERROR=" + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
