#!/usr/bin/env python3
"""Verify retained external evidence and Git source identity without executing Lean."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(evidence: Path, source_commit: str) -> dict:
    repo = Path(__file__).resolve().parents[3]
    spec = importlib.util.spec_from_file_location(
        "gr_strengthening_axiom_parser", repo / "Auxillary/scripts/verify_audit.py")
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    summary = json.loads((evidence / "audit-summary.json").read_text())
    provenance = json.loads((evidence / "provenance.json").read_text())
    manifest = json.loads((evidence / "source-manifest.json").read_text())
    assert re.fullmatch(r"[a-f0-9]{40}", source_commit)
    assert summary["source_commit"] == provenance["source_commit"] == manifest["source_commit"] == source_commit
    assert summary["source_input_verification"] == "PASS"
    assert provenance["external_platform"] == "linux"
    assert provenance["requested_toolchain"] == parser.EXPECTED_LEAN
    assert summary["actual_mathlib_commit"] == parser.EXPECTED_MATHLIB
    assert "version 4.34.0-rc1," in summary["actual_lean_version"]
    assert "3447a668783dbce1a8fdb97101dd067687b2b418" in summary["actual_lean_version"]
    assert digest(evidence / "source-manifest.json") == summary["source_manifest_sha256"]
    assert summary["source_manifest_sha256"] == provenance["source_manifest_sha256"]
    assert summary["github_run_id"] == provenance["github_run_id"]
    assert summary["github_run_attempt"] == provenance["github_run_attempt"]
    for command in provenance["commands"]:
        assert digest(evidence / command["log"]) == command["sha256"], command["log"]
    for row in manifest["files"]:
        content = subprocess.check_output(["git", "show", source_commit + ":" + row["path"]], cwd=repo)
        assert hashlib.sha256(content).hexdigest() == row["sha256"], row["path"]
    declared = {row["name"]: row for row in summary["declarations"]}
    assert len(declared) == len(summary["declarations"])
    verified = []
    for module in summary["modules"]:
        if module["audit_status"] != "PASS_STANDARD_ONLY":
            continue
        assert module["build_status"] == "PASS"
        assert module["freshness_exit_code"] == module["audit_exit_code"] == 0
        assert re.fullmatch(r"[a-f0-9]{64}", module["olean_sha256"])
        assert digest(evidence / module["audit_source"]) == module["audit_source_sha256"]
        records = parser.parse_axioms((evidence / module["audit_log"]).read_text())
        assert set(records) == set(module["audit_targets"])
        for name, rows in records.items():
            assert len(rows) == 1, name
            axioms = sorted(parser.normalize_axiom_name(item) for item in rows[0])
            assert not set(axioms) - parser.ALLOWED_AXIOMS, name
            row = declared[name]
            assert row["status"] == "PASS_STANDARD_ONLY" and not row["unapproved_axioms"]
            assert row["axioms"] == axioms and row["module"] == module["module"]
            verified.append(name)
    expected = {name for name, row in declared.items() if row["status"] == "PASS_STANDARD_ONLY"}
    assert set(verified) == expected
    return {
        "status": "VERIFIED_EXTERNAL_COMPILATION_AND_EXACT_AXIOM_RECORDS",
        "source_commit": source_commit,
        "run_id": summary["github_run_id"],
        "run_attempt": summary["github_run_attempt"],
        "source_files_verified": len(manifest["files"]),
        "verified_declarations": sorted(verified),
        "local_lean_executions": 0,
        "unapproved_axioms": [],
        "semantic_scope": "EXACT_AUDITED_IMPLICATIONS; EXPLICIT_PREMISES_ARE_NOT_DISCHARGED_BY_AUDIT",
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--evidence", required=True, type=Path)
    cli.add_argument("--source-commit", required=True)
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    result = verify(args.evidence, args.source_commit)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "verified_declarations"}
        | {"verified_declaration_count": len(result["verified_declarations"])}, indent=2))
