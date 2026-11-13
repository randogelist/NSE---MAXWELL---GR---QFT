#!/usr/bin/env python3
"""Verify external compiler provenance and exact theorem-level axiom records.

This verifier never executes Lean. It does not infer analytic premise discharge
from an axiom audit. The external native Windows or Linux runner supplies compiler output.
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
AXIOM_NAME = re.compile(
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
    r"(?:\.\{(?P<universes>[^{}]+)\})?\Z"
)
UNIVERSE_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[()+,]")


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


def split_axiom_list(text: str) -> list[str]:
    """Split declaration entries, preserving commas inside universe braces."""
    if not text.strip():
        return []
    result: list[str] = []
    depth = 0
    start = 0
    for index, char in enumerate(text):
        if char == "{":
            depth += 1
            if depth > 1:
                raise ValueError("Nested braces in an axiom universe suffix.")
        elif char == "}":
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced braces in an axiom record.")
        elif char == "," and depth == 0:
            result.append(text[start:index].strip())
            start = index + 1
    if depth:
        raise ValueError("Unbalanced braces in an axiom record.")
    result.append(text[start:].strip())
    if any(not item for item in result):
        raise ValueError("Empty declaration entry in an axiom record.")
    return result


def validate_universes(text: str) -> None:
    """Recognize universe parameters, numerals, max/imax, and successors.

    Unsupported or malformed renderings fail closed. No declaration-name text
    outside the terminal universe suffix is discarded.
    """
    tokens: list[str] = []
    end = 0
    for match in UNIVERSE_TOKEN.finditer(text):
        if text[end:match.start()].strip():
            raise ValueError(f"Invalid universe-instantiation suffix: {text!r}")
        tokens.append(match.group())
        end = match.end()
    if text[end:].strip() or not tokens:
        raise ValueError(f"Invalid universe-instantiation suffix: {text!r}")
    position = 0

    def level(depth: int = 0) -> None:
        nonlocal position
        if depth > 32 or position >= len(tokens):
            raise ValueError(f"Malformed universe expression: {text!r}")
        token = tokens[position]
        position += 1
        if token in {"max", "imax"}:
            level(depth + 1)
            level(depth + 1)
        elif token == "(":
            level(depth + 1)
            if position >= len(tokens) or tokens[position] != ")":
                raise ValueError(f"Unclosed universe expression: {text!r}")
            position += 1
        elif token in {")", "+", ","}:
            raise ValueError(f"Malformed universe expression: {text!r}")
        while position < len(tokens) and tokens[position] == "+":
            position += 1
            if position >= len(tokens) or not tokens[position].isdigit():
                raise ValueError(f"Invalid universe successor: {text!r}")
            position += 1

    level()
    while position < len(tokens):
        if tokens[position] != ",":
            raise ValueError(f"Unexpected universe token: {text!r}")
        position += 1
        level()


def normalize_axiom_name(rendered: str) -> str:
    """Remove only a well-formed terminal .{...} universe instantiation."""
    match = AXIOM_NAME.fullmatch(rendered)
    if match is None:
        raise ValueError(f"Malformed rendered axiom name: {rendered!r}")
    universes = match.group("universes")
    if universes is not None:
        validate_universes(universes)
    return match.group("name")


def parse_axioms(log: str) -> dict[str, list[set[str]]]:
    result: dict[str, list[set[str]]] = {}
    for match in AXIOM_RECORD.finditer(ANSI.sub("", log)):
        raw = match.group("axioms")
        axioms = set() if raw is None else set(split_axiom_list(raw))
        result.setdefault(match.group("name"), []).append(axioms)
    return result


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in (
        "root", "targets", "audit-source", "log", "manifest",
        "provenance", "scope", "output",
    ):
        parser.add_argument(f"--{name}", required=True, type=Path)
    parser.add_argument(
        "--expected-platform", choices=("windows", "linux"), default="windows",
        help="Required native compiler platform; the default preserves historical Windows audits.",
    )
    return parser.parse_args()


def platform_errors(provenance: dict[str, object], expected_platform: str) -> list[str]:
    """Check native-host flags and the actual Lean target, retaining legacy Windows evidence."""
    if expected_platform not in {"windows", "linux"}:
        raise ValueError("Unsupported expected compiler platform.")
    errors: list[str] = []
    actual_platform = provenance.get("external_platform")
    if actual_platform is None and provenance.get("external_native_windows") is True:
        actual_platform = "windows"
    if actual_platform != expected_platform:
        errors.append(f"External native {expected_platform} compiler provenance is required.")
    windows = provenance.get("external_native_windows") is True
    linux = provenance.get("external_native_linux") is True
    if (windows, linux) != (expected_platform == "windows", expected_platform == "linux"):
        errors.append("Native platform flags are absent, inconsistent, or do not match the requested platform.")
    version = str(provenance.get("actual_lean_version", ""))
    target = re.search(r"version 4\.34\.0-rc1,\s*([^,\s]+)", version)
    if target is None or f"-{expected_platform}-" not in target.group(1):
        errors.append("The actual Lean compiler target does not match the required native platform.")
    return errors


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

    expected_platform = getattr(args, "expected_platform", "windows")
    errors: list[str] = platform_errors(provenance, expected_platform)
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
        rendered_axioms = found[0]
        axioms: set[str] = set()
        malformed: list[str] = []
        for rendered in sorted(rendered_axioms):
            try:
                axioms.add(normalize_axiom_name(rendered))
            except ValueError:
                malformed.append(rendered)
        if malformed:
            errors.append(f"Malformed axiom names for {name}: {malformed!r}")
        unapproved = sorted(axioms - ALLOWED_AXIOMS)
        if unapproved:
            errors.append(f"Unapproved axioms for {name}: {', '.join(unapproved)}")
        theorems.append({
            "name": name,
            "status": "FAIL" if unapproved or malformed else "PASS_STANDARD_ONLY",
            "axioms": sorted(axioms),
            "rendered_axioms": sorted(rendered_axioms),
            "unapproved_axioms": unapproved,
            "malformed_axioms": malformed,
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
        "lean-toolchain", "lakefile.lean", "lake-manifest.json",
        "Fefferman_B_adapter/NSEMaxwell.lean",
        "Fefferman_B_adapter/NSEMaxwell/Audit.lean",
        "audit-targets.txt", "formalization-status.json",
        "Fefferman_B_adapter/scripts/run.ps1",
        "Fefferman_B_adapter/scripts/verify_audit.py", "run.cmd",
        "B <-> Maxwell/=>/NSEMaxwellForward.lean",
        "B <-> Maxwell/=>/NSEMaxwellForward/Reduced.lean",
        "B <-> Maxwell/<=/NSEMaxwellReverse.lean",
        "B <-> Maxwell/<=/NSEMaxwellReverse/Reduced.lean",
    }
    for source_root in (
        "Fefferman_B_adapter", "B <-> Maxwell/=>", "B <-> Maxwell/<=",
    ):
        directory = root / source_root
        if not directory.is_dir():
            manifest_errors.append(f"Active project source root is absent: {source_root}")
            continue
        required.update(
            path.relative_to(root).as_posix()
            for path in directory.rglob("*.lean") if path.is_file()
        )
    if expected_platform == "linux":
        required.add("run.sh")
    for relative in sorted(required - paths_seen):
        manifest_errors.append(f"Source manifest omits required input: {relative}")
    errors.extend(manifest_errors)

    return {
        "schema_version": 1,
        "status": "FAIL" if errors else "PASS_STANDARD_ONLY",
        "source_commit": provenance.get("source_commit"),
        "source_manifest_sha256": manifest_hash,
        "external_compiler_status": provenance.get("build_status"),
        "expected_platform": expected_platform,
        "external_platform": provenance.get("external_platform") or (
            "windows" if provenance.get("external_native_windows") is True else None
        ),
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
