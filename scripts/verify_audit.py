#!/usr/bin/env python3
"""Verify external compiler provenance and exact theorem-level axiom records.

This verifier never executes Lean. It does not infer analytic premise discharge
from an axiom audit. The external native Windows runner supplies compiler output.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXPECTED_LEAN = "leanprover/lean4:v4.34.0-rc1"
EXPECTED_MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
AXIOM_RECORD = re.compile(
    r"['\u2018](?P<name>[^'\u2019\r\n]+)['\u2019]\s+"
    r"(?:does not depend on any axioms|"
    r"depends on axioms:\s*\[(?P<axioms>[^\]]*)\])",
    re.MULTILINE,
)
DECL_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")


def read_text(path: Path) -> str:
    data = path.read_bytes()
    if data.startswith((b"\xff\xfe", b"\xfe\xff")):
        return data.decode("utf-16")
    return data.decode("utf-8-sig")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_targets(path: Path) -> list[str]:
    targets = [
        line.strip()
        for line in read_text(path).splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if not targets:
        raise ValueError("No theorem audit targets were specified.")
    if len(targets) != len(set(targets)):
        raise ValueError("Duplicate theorem audit targets.")
    invalid = [name for name in targets if not DECL_NAME.fullmatch(name)]
    if invalid:
        raise ValueError(f"Invalid theorem audit names: {invalid!r}")
    return targets


def parse_axioms(log: str) -> dict[str, list[set[str]]]:
    result: dict[str, list[set[str]]] = {}
    for match in AXIOM_RECORD.finditer(ANSI.sub("", log)):
        raw = match.group("axioms")
        axioms = set() if raw is None else {
            name.strip() for name in raw.split(",") if name.strip()
        }
        result.setdefault(match.group("name"), []).append(axioms)
    return result


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in (
        "root", "targets", "audit-source", "log", "manifest",
        "provenance", "scope", "output",
    ):
        parser.add_argument(f"--{name}", required=True, type=Path)
    return parser.parse_args()


def verify(args: argparse.Namespace) -> dict[str, object]:
    root = args.root.resolve()

    def at_root(path: Path) -> Path:
        return path if path.is_absolute() else root / path

    targets = parse_targets(at_root(args.targets))
    audit_source = read_text(at_root(args.audit_source))
    log = ANSI.sub("", read_text(at_root(args.log)))
    provenance = json.loads(read_text(at_root(args.provenance)))
    manifest_path = at_root(args.manifest)
    manifest = json.loads(read_text(manifest_path))
    scope = json.loads(read_text(at_root(args.scope)))
    if not isinstance(provenance, dict):
        raise ValueError("Compiler provenance must be a JSON object.")
    if not isinstance(manifest, dict) or not isinstance(manifest.get("files"), list):
        raise ValueError("Source manifest must contain a files array.")
    if not isinstance(scope, dict) or not scope:
        raise ValueError("Declared formalization scope must be a nonempty JSON object.")

    errors: list[str] = []
    if provenance.get("external_native_windows") is not True:
        errors.append("External native Windows compiler evidence is required.")
    if provenance.get("requested_toolchain") != EXPECTED_LEAN:
        errors.append("Unexpected requested Lean toolchain.")
    if not re.search(
        r"version 4\.34\.0-rc1(?:,|\))", str(provenance.get("actual_lean_version", ""))
    ):
        errors.append("Matching Lean 4.34.0-rc1 compiler-version evidence is absent.")
    if provenance.get("actual_mathlib_commit") != EXPECTED_MATHLIB:
        errors.append("Mathlib revision does not match the pinned revision.")
    if provenance.get("build_status") != "PASS":
        errors.append("A successful project build is required.")
    if provenance.get("audit_command_status") != "PASS":
        errors.append("A successful Lean audit command is required.")

    commands = re.findall(
        r"^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$",
        audit_source,
        re.MULTILINE,
    )
    checks = re.findall(
        r"^\s*#check\s+@?([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$",
        audit_source,
        re.MULTILINE,
    )
    if len(commands) != len(targets) or set(commands) != set(targets):
        errors.append("Audit source must print axioms exactly once for every target.")
    if len(checks) != len(targets) or set(checks) != set(targets):
        errors.append("Audit source must print the full signature of every target.")
    if "sorryAx" in log or re.search(r"declaration uses ['\u2018]sorry", log):
        errors.append("An admission or sorryAx occurs in the compiler audit output.")
    if re.search(r"(?:^|\n).*:\s*error:", log):
        errors.append("A Lean error occurs in the compiler audit output.")

    records = parse_axioms(log)
    theorems: list[dict[str, object]] = []
    for name in targets:
        found = records.get(name, [])
        if len(found) != 1:
            errors.append(f"Expected one axiom record for {name}; found {len(found)}.")
            theorems.append({"name": name, "status": "MISSING_OR_DUPLICATE"})
            continue
        axioms = found[0]
        unapproved = sorted(axioms - ALLOWED_AXIOMS)
        if unapproved:
            errors.append(f"Unapproved axioms for {name}: {', '.join(unapproved)}")
        theorems.append({
            "name": name,
            "status": "FAIL" if unapproved else "PASS_STANDARD_ONLY",
            "axioms": sorted(axioms),
            "unapproved_axioms": unapproved,
        })

    manifest_errors: list[str] = []
    manifest_hash = sha256(manifest_path)
    if provenance.get("source_manifest_sha256") != manifest_hash:
        manifest_errors.append("Source manifest hash differs from compiler provenance.")
    paths_seen: set[str] = set()
    for item in manifest["files"]:
        if not isinstance(item, dict):
            manifest_errors.append("Invalid source manifest item.")
            continue
        relative = item.get("path")
        expected = item.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected, str):
            manifest_errors.append("Source manifest entries require path and SHA-256.")
            continue
        if relative in paths_seen:
            manifest_errors.append(f"Duplicate source manifest entry: {relative}")
        paths_seen.add(relative)
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            manifest_errors.append(f"Missing or invalid source manifest input: {relative}")
        elif sha256(path) != expected.lower():
            manifest_errors.append(f"Source input changed during compilation: {relative}")
    required = {
        "lean-toolchain", "lake-manifest.json", "NSEMaxwell.lean",
        "NSEMaxwell/Audit.lean", "audit-targets.txt", "formalization-status.json",
        "scripts/run.ps1", "scripts/verify_audit.py", "run.cmd",
    }
    for relative in sorted(required - paths_seen):
        manifest_errors.append(f"Source manifest omits required input: {relative}")
    errors.extend(manifest_errors)

    return {
        "schema_version": 1,
        "status": "FAIL" if errors else "PASS_STANDARD_ONLY",
        "source_commit": provenance.get("source_commit"),
        "source_manifest_sha256": manifest_hash,
        "external_compiler_status": provenance.get("build_status"),
        "audit_command_status": provenance.get("audit_command_status"),
        "source_input_verification": "FAIL" if manifest_errors else "PASS",
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "theorems": theorems,
        "declared_formalization_scope": scope,
        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
        "exact_root_promotion": "REQUIRES_SEPARATE_SCOPE_AND_PREMISE_REVIEW",
        "errors": errors,
    }


def main() -> int:
    args = arguments()
    try:
        report = verify(args)
    except (OSError, ValueError, TypeError, KeyError) as error:
        report = {
            "schema_version": 1,
            "status": "FAIL",
            "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
            "exact_root_promotion": "REQUIRES_SEPARATE_SCOPE_AND_PREMISE_REVIEW",
            "errors": [str(error)],
        }
    output = args.output if args.output.is_absolute() else args.root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"THEOREM_AXIOM_AUDIT={report['status']}")
    for error in report["errors"]:
        print(f"ERROR: {error}", file=sys.stderr)
    print("SEMANTIC_DISCHARGE=NOT_INFERRED_FROM_AXIOM_AUDIT")
    print("EXACT_ROOT_PROMOTION=REQUIRES_SEPARATE_SCOPE_AND_PREMISE_REVIEW")
    return 0 if report["status"] == "PASS_STANDARD_ONLY" else 1


if __name__ == "__main__":
    raise SystemExit(main())
