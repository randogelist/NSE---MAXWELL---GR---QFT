#!/usr/bin/env python3
"""External-only native GR build and named theorem audit; never cleans caches.

Run this script only on the user's native compiler or GitHub Actions runner.
Authoring/checking this source does not authorize local Lean execution.
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
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
STAGES = (("adapter", "GRAdapter"), ("forward", "NSEGRForward"),
          ("reverse", "NSEGRReverse"))
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
RECORD = re.compile(r"['‘](?P<name>[^'’\r\n]+)['’]\s+"
                    r"(?:does not depend on any axioms|depends on axioms:\s*"
                    r"\[(?P<axioms>[^\]]*)\])", re.MULTILINE)
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def audit_records(log: str, targets: list[str]) -> list[dict]:
    """Require one exact standard-only axiom record for every named target."""
    text = ANSI.sub("", log)
    require("sorryAx" not in text, "sorryAx in theorem audit output")
    require(not re.search(r"declaration uses ['‘]sorry", text), "sorry declaration")
    require(not re.search(r"(?:^|\n).*:\s*error:", text), "Lean error in audit output")
    records: dict[str, list[set[str]]] = {}
    for match in RECORD.finditer(text):
        values = set(filter(None, (x.strip() for x in (match.group("axioms") or "").split(","))))
        records.setdefault(match.group("name"), []).append(values)
    result = []
    for name in targets:
        found = records.get(name, [])
        require(len(found) == 1, f"Expected exactly one axiom record: {name}; got {len(found)}")
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
    args = parser.parse_args()
    package = args.package_root.resolve()
    repo = package.parent
    support = repo / "Auxillary" / "GR"
    report = (args.report_directory or repo / "artifacts" / "gr-external").resolve()
    report.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["ELAN_TOOLCHAIN"] = TOOLCHAIN
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    provenance: dict = {
        "schema_version": 1,
        "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "source_commit": args.source_commit,
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "requested_toolchain": TOOLCHAIN,
        "requested_mathlib_commit": MATHLIB,
        "external_platform": platform.system().lower(),
        "phase": args.phase,
        "cache_policy": "PRESERVE_AND_REUSE_COMPATIBLE_OBJECTS",
        "stages": {}, "commands": [], "status": "RUNNING",
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
        "exact_root_promotion": "REQUIRES_MATCHING_TYPE_AND_PREMISE_REVIEW",
    }

    def persist() -> None:
        write_json(report / ("provenance-" + args.phase + ".json"), provenance)

    def run(command: list[str], log_name: str, cwd: Path = package) -> str:
        log_path = report / log_name
        started = time.monotonic()
        output: list[str] = []
        print("COMMAND=" + " ".join(command), flush=True)
        with log_path.open("w", encoding="utf-8") as log:
            proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                                    errors="replace")
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

    def verify_dependencies() -> list[dict]:
        result = []
        for entry in manifest["packages"]:
            require(entry["type"] == "git" and re.fullmatch(r"[a-f0-9]{40}", entry["rev"]) is not None,
                    "Every dependency must be an immutable git revision")
            name = entry["name"]
            require(re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None, "Invalid dependency name")
            checkout = package / ".lake" / "packages" / name
            revision = run(["git", "-C", str(checkout), "rev-parse", "HEAD"], f"dependency-{name}-revision.log").strip()
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
        provenance["actual_lean_version"] = version.strip()
        if args.phase in {"all", "dependencies"}:
            run(["lake", "env", "lean", "--version"], "dependency-resolution.log")
            require(digest(lock) == lock_hash, "Dependency resolution changed the committed lock")
            provenance["dependency_revisions"] = verify_dependencies()
            run(["lake", "exe", "cache", "get", "Mathlib"], "mathlib-cache-get.log")
            require(digest(lock) == lock_hash, "Cache acquisition changed the committed lock")
            provenance["dependency_status"] = "PASS"
            persist()
        if args.phase == "dependencies":
            provenance["status"] = "PASS"
            persist()
            return 0

        provenance["dependency_revisions"] = verify_dependencies()
        provenance["actual_mathlib_commit"] = MATHLIB
        inventories = json.loads((support / "audit-targets.json").read_text())
        require(set(inventories) == {name for name, _ in STAGES}, "Three exact audit stage inventories required")
        all_targets: list[str] = []
        for stage, _ in STAGES:
            names = inventories[stage]
            require(isinstance(names, list) and names, f"Nonempty audit inventory required: {stage}")
            require(all(isinstance(name, str) and NAME.fullmatch(name) for name in names), "Invalid target name")
            all_targets.extend(names)
        require(len(set(all_targets)) == len(all_targets), "Duplicate named audit targets")
        scope_path = support / "formalization-status.json"
        scope = json.loads(scope_path.read_text())
        require(isinstance(scope, dict) and scope, "Nonempty exact formalization scope required")

        inputs = sorted({p for p in package.rglob("*.lean") if ".lake" not in p.parts}
            | {package / "lean-toolchain", package / "lakefile.lean", lock,
               package / "run.sh", package / "run.cmd", Path(__file__).resolve(),
               support / "audit-targets.json", scope_path})
        source_manifest = {"source_commit": args.source_commit,
            "files": [{"path": p.relative_to(repo).as_posix(), "sha256": digest(p)} for p in inputs]}
        write_json(report / "source-manifest.json", source_manifest)
        provenance["source_manifest_sha256"] = digest(report / "source-manifest.json")
        write_json(report / "declared-scope.json", scope)
        summaries = []
        for stage, module in STAGES:
            provenance["stages"][stage] = {"build": "RUNNING", "audit": "NOT_RUN"}
            persist()
            run(["lake", "build", module], stage + "-build.log")
            provenance["stages"][stage]["build"] = "PASS"
            audit = report / (stage.capitalize() + "Audit.lean")
            source = "import " + module + "\nset_option pp.universes true\nset_option pp.width 160\n"
            for name in inventories[stage]:
                source += "#check @" + name + "\n#print axioms " + name + "\n"
            audit.write_text(source, encoding="utf-8")
            log = run(["lake", "env", "lean", "-R", str(report), str(audit)], stage + "-audit.log")
            records = audit_records(log, inventories[stage])
            stage_report = {"stage": stage, "module": module, "status": "PASS_STANDARD_ONLY",
                "source_commit": args.source_commit, "target_count": len(records),
                "audit_source_sha256": digest(audit), "audit_log_sha256": digest(report / (stage + "-audit.log")),
                "targets": records, "hypothesis_discharge": "NOT_INFERRED"}
            write_json(report / (stage + "-summary.json"), stage_report)
            summaries.append(stage_report)
            provenance["stages"][stage]["audit"] = "PASS_STANDARD_ONLY"
            persist()
            print(f"GR_STAGE={stage}; BUILD=PASS; NAMED_AXIOM_AUDIT={len(records)}/{len(records)} STANDARD_ONLY", flush=True)

        require(digest(lock) == lock_hash, "Build changed the committed lock")
        for item in source_manifest["files"]:
            require(digest(repo / item["path"]) == item["sha256"], "Source input changed during external run: " + item["path"])
        summary = {"schema_version": 1, "status": "PASS_STANDARD_ONLY", "source_commit": args.source_commit,
            "actual_lean_version": provenance["actual_lean_version"], "actual_mathlib_commit": MATHLIB,
            "source_manifest_sha256": provenance["source_manifest_sha256"], "source_input_verification": "PASS",
            "target_count": len(all_targets), "allowed_axioms": sorted(ALLOWED), "stages": summaries,
            "declared_scope": scope, "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"}
        write_json(report / "audit-summary.json", summary)
        provenance["status"] = "PASS_STANDARD_ONLY"
        persist()
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        provenance["status"] = "FAIL"
        provenance["error"] = str(error)
        persist()
        print("GR_EXTERNAL_ERROR=" + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
