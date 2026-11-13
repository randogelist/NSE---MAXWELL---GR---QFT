#!/usr/bin/env python3
"""Verify downloaded GR assembly evidence against exact current source bytes.

This verifier is Python-only: it never invokes Lean, Lake, elan, Git, or a shell.
Successful evidence verifies the named implications, not discharge of premises.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path, PurePosixPath
import re
import sys

sys.dont_write_bytecode = True
from run_assembly import (  # noqa: E402
    ALLOWED, ANSI, COMPILER_COMMIT, MATHLIB, NAME, RECORD, SOURCE_NAME,
    TOOLCHAIN, audit_records, digest, require,
)

SHA256 = re.compile(r"[a-f0-9]{64}\Z")
COMMIT = re.compile(r"[a-f0-9]{40}\Z")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError("Non-finite JSON value: " + value)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=unique_object, parse_constant=reject_constant)


def contained_file(root: Path, value: str) -> Path:
    require(isinstance(value, str) and bool(value), "Empty or non-string evidence path")
    relative = PurePosixPath(value)
    require(not relative.is_absolute() and ".." not in relative.parts and "\\" not in value,
            "Non-relative evidence path: " + value)
    require(relative.as_posix() == value and relative.parts, "Non-canonical evidence path: " + value)
    path = root.joinpath(*relative.parts)
    require(path.resolve().is_relative_to(root), "Path escapes the declared root: " + value)
    require(path.is_file(), "Missing file: " + str(path))
    return path


def current_source_paths(repo: Path) -> set[str]:
    """Mirror the runner's declared inputs; no evidence-manifest entry is skipped."""
    paths = set()
    for name in ("ASSEMBLY", "GR_adapter", "TEMP"):
        source_root = repo / name
        require(source_root.is_dir(), "Missing source directory: " + name)
        for suffix in ("*.lean", "*.json"):
            paths.update(p for p in source_root.rglob(suffix)
                         if ".lake" not in p.parts and "__pycache__" not in p.parts)
        paths.add(source_root / "lean-toolchain")
    paths.update(repo / path for path in (
        "ASSEMBLY/run.cmd", "ASSEMBLY/run.sh",
        "Auxillary/GR/Assembly/scripts/run_assembly.py",
        "Auxillary/GR/Assembly/audit-targets.json",
        "Auxillary/GR/Assembly/formalization-status.json",
        "Auxillary/GR/audit-targets.json", "Auxillary/TEMP/audit-targets.json",
    ))
    return {path.relative_to(repo).as_posix() for path in paths}


def check_inventory(entries, label: str) -> list[str]:
    require(isinstance(entries, list) and bool(entries), "Empty/non-list " + label + " inventory")
    require(all(isinstance(x, dict) for x in entries), "Malformed " + label + " inventory")
    require(all(isinstance(x.get("name"), str) and SOURCE_NAME.fullmatch(x["name"])
                and isinstance(x.get("module"), str) and NAME.fullmatch(x["module"])
                for x in entries), "Invalid " + label + " declaration/module name")
    names = [x["name"] for x in entries]
    require(len(set(names)) == len(names), "Duplicate " + label + " target")
    return names


def verify(repo: Path, evidence: Path, requested_commit: str | None) -> dict:
    require(repo.is_dir() and evidence.is_dir(), "Repository and evidence directories must exist")
    summary = read_json(contained_file(evidence, "audit-summary.json"))
    require(isinstance(summary, dict), "Malformed audit summary")
    require(summary["schema_version"] == 1, "Unsupported audit-summary schema")
    require(summary["status"] == "PASS_STANDARD_ONLY", "Assembly audit did not pass")
    source_commit = summary["source_commit"]
    require(isinstance(source_commit, str) and COMMIT.fullmatch(source_commit), "Invalid source commit")
    if requested_commit is not None:
        require(COMMIT.fullmatch(requested_commit), "--source-commit must be a full lowercase Git SHA")
        require(source_commit == requested_commit, "Evidence source commit mismatch")
    require(summary["source_input_verification"] == "PASS", "Source inputs were not verified")
    require(summary["actual_mathlib_commit"] == MATHLIB, "Evidence Mathlib pin mismatch")
    require(summary["allowed_axioms"] == sorted(ALLOWED), "Approved axiom set mismatch")
    require(summary["semantic_discharge"] == "NOT_INFERRED_FROM_AXIOM_AUDIT",
            "Unexpected semantic-discharge claim")

    manifest_path = contained_file(evidence, "source-manifest.json")
    require(summary["source_manifest_sha256"] == digest(manifest_path), "Source-manifest hash mismatch")
    manifest = read_json(manifest_path)
    require(manifest["source_commit"] == source_commit, "Source-manifest commit mismatch")
    require(manifest["source_roots"] == ["ASSEMBLY", "GR_adapter", "TEMP"], "Source roots mismatch")
    entries = manifest["files"]
    require(isinstance(entries, list) and bool(entries), "Empty source manifest")
    declared_paths = []
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"path", "sha256"}, "Malformed source-manifest entry")
        path = contained_file(repo, entry["path"])
        require(isinstance(entry["sha256"], str) and SHA256.fullmatch(entry["sha256"]), "Invalid source hash")
        require(digest(path) == entry["sha256"], "Source bytes differ: " + entry["path"])
        declared_paths.append(entry["path"])
    require(len(set(declared_paths)) == len(declared_paths), "Duplicate source-manifest path")
    expected_paths = current_source_paths(repo)
    require(set(declared_paths) == expected_paths,
            "Source-manifest coverage mismatch; missing=" + repr(sorted(expected_paths - set(declared_paths)))
            + "; unexpected=" + repr(sorted(set(declared_paths) - expected_paths)))

    require((repo / "ASSEMBLY/lean-toolchain").read_text().strip() == TOOLCHAIN, "Current toolchain pin mismatch")
    lock = read_json(repo / "ASSEMBLY/lake-manifest.json")
    locked = lock["packages"]
    require(isinstance(locked, list) and bool(locked), "Empty dependency lock")
    require(all(isinstance(x, dict) and x.get("type") == "git" and isinstance(x.get("rev"), str)
                and COMMIT.fullmatch(x["rev"]) and isinstance(x.get("name"), str)
                for x in locked), "Non-immutable dependency lock")
    require(len({x["name"] for x in locked}) == len(locked), "Duplicate dependency lock entry")
    require([x["rev"] for x in locked if x["name"] == "mathlib"] == [MATHLIB], "Current Mathlib pin mismatch")

    baseline = read_json(repo / "Auxillary/GR/audit-targets.json")
    require(isinstance(baseline, dict) and set(baseline) == {"adapter", "forward", "reverse"},
            "Unexpected baseline inventory")
    require(all(isinstance(names, list) and names
                and all(isinstance(n, str) and SOURCE_NAME.fullmatch(n) for n in names)
                for names in baseline.values()), "Invalid baseline declarations")
    baseline_names = [name for names in baseline.values() for name in names]
    require(len(baseline_names) == 401 and len(set(baseline_names)) == 401, "Baseline target count mismatch")
    cutouts = read_json(repo / "Auxillary/TEMP/audit-targets.json")
    cutout_names = check_inventory(cutouts, "cutout")
    require(len(cutout_names) == 85, "Cutout target count mismatch")
    cutout_imports = set(re.findall(r"^import\s+(\S+)\s*$",
        (repo / "TEMP/TempEndpoints.lean").read_text(), re.MULTILINE))
    require({x["module"] for x in cutouts} <= cutout_imports, "Missing TempEndpoints import")
    inventory = read_json(repo / "Auxillary/GR/Assembly/audit-targets.json")
    assembly_names = check_inventory(inventory, "assembly")
    require(all(x["module"].startswith("GRAssembly") for x in inventory), "Unexpected assembly module")
    all_names = baseline_names + cutout_names + assembly_names
    require(len(set(all_names)) == len(all_names), "Targets overlap across stages")
    for key, count in (("baseline_target_count", 401), ("cutout_target_count", 85),
                       ("new_target_count", len(assembly_names)), ("target_count", len(all_names))):
        require(type(summary[key]) is int and summary[key] == count, "Summary count mismatch: " + key)

    scope = read_json(contained_file(evidence, "declared-scope.json"))
    current_scope = read_json(repo / "Auxillary/GR/Assembly/formalization-status.json")
    current_scope.update({"selected_modules": sorted({x["module"] for x in inventory}),
        "selected_new_target_count": len(inventory), "full_new_target_count": len(inventory),
        "baseline_target_count": 401, "cutout_target_count": len(cutouts),
        "cutout_validation": "FRESH_NAMED_AXIOM_AUDITS; SOURCE_TYPE_EQUALITY_RETAINS_PRIOR_CERTIFICATE",
        "selection_mode": "full"})
    require(scope == current_scope and summary["declared_scope"] == scope,
            "Declared scope differs from exact full current inventory")

    provenance_files = [name for name in ("provenance-build.json", "provenance-all.json")
                        if (evidence / name).is_file()]
    require(len(provenance_files) == 1, "Expected exactly one build/all provenance record")
    provenance = read_json(contained_file(evidence, provenance_files[0]))
    phase = provenance_files[0][len("provenance-"):-len(".json")]
    require(provenance["phase"] == phase and provenance["schema_version"] == 1, "Provenance phase/schema mismatch")
    require(provenance["status"] == "PASS_STANDARD_ONLY", "Build provenance did not pass")
    require(provenance["source_commit"] == source_commit, "Provenance source commit mismatch")
    require(provenance["requested_toolchain"] == TOOLCHAIN, "Provenance toolchain mismatch")
    require(provenance["requested_compiler_commit"] == COMPILER_COMMIT, "Compiler commit pin mismatch")
    require(provenance["requested_mathlib_commit"] == MATHLIB
            and provenance["actual_mathlib_commit"] == MATHLIB, "Provenance Mathlib pin mismatch")
    require(provenance["source_manifest_sha256"] == digest(manifest_path), "Provenance manifest hash mismatch")
    require(provenance["cache_policy"] == "PRESERVE_AND_REUSE_COMPATIBLE_OBJECTS", "Cache policy mismatch")
    require(provenance["semantic_discharge"] == "NOT_INFERRED_FROM_AXIOM_AUDIT", "Provenance semantic claim mismatch")
    require(provenance["root_promotion"] == "REQUIRES_EXACT_ROOT_TYPE_AND_PREMISE_REVIEW", "Root promotion policy mismatch")
    native_platform = provenance["external_platform"]
    require(native_platform in {"linux", "windows"}, "Unexpected external compiler platform")
    version = summary["actual_lean_version"]
    require(isinstance(version, str) and re.search(r"version 4\.34\.0-rc1,\s*[^,\s]*-"
            + native_platform + r"-[^,\s]*,", version), "Actual compiler version/target mismatch")
    require(re.search(r"\bcommit\s+" + COMPILER_COMMIT + r"\b", version),
            "Actual compiler commit mismatch")
    require(provenance["actual_lean_version"] == version, "Compiler version records disagree")
    require(contained_file(evidence, "lean-version-" + phase + ".log").read_text().strip() == version,
            "Raw compiler version differs from summary")
    require(provenance["dependency_revisions"] == [{"name": x["name"], "revision": x["rev"]} for x in locked],
            "Verified dependency revisions differ from lock")
    for dependency in locked:
        name = dependency["name"]
        require(re.fullmatch(r"[A-Za-z0-9_-]+", name), "Invalid dependency name")
        require(contained_file(evidence, f"dependency-{name}-revision.log").read_text().strip() == dependency["rev"],
                "Raw dependency revision mismatch: " + name)
        require(not contained_file(evidence, f"dependency-{name}-working-tree.log").read_text().strip(),
                "Dirty dependency evidence: " + name)

    stages = [("adapter", "GRAdapter", baseline["adapter"]),
              ("forward", "NSEGRForward", baseline["forward"]),
              ("reverse", "NSEGRReverse", baseline["reverse"]),
              ("cutouts", "TempEndpoints", cutout_names),
              ("assembly", "GRAssembly", assembly_names)]
    require(isinstance(summary["stages"], list) and len(summary["stages"]) == len(stages), "Incomplete stage list")
    require(provenance["stages"] == summary["stages"], "Provenance and summary stages disagree")
    commands = provenance["commands"]
    require(isinstance(commands, list) and bool(commands), "Missing command provenance")
    require(all(isinstance(c, dict) and type(c.get("exit_code")) is int and c["exit_code"] == 0
                and isinstance(c.get("command"), list) and isinstance(c.get("log"), str)
                for c in commands), "Failed/malformed provenance command")
    stage_command_indices = []
    for entry, (stage, module, names) in zip(summary["stages"], stages):
        require(isinstance(entry, dict) and entry["stage"] == stage and entry["module"] == module,
                "Unexpected stage order/module: " + stage)
        require(entry["status"] == "PASS_STANDARD_ONLY" and entry["source_commit"] == source_commit,
                "Unsuccessful/mismatched stage: " + stage)
        require(type(entry["target_count"]) is int and entry["target_count"] == len(names),
                "Stage target count mismatch: " + stage)
        require(read_json(contained_file(evidence, stage + "-summary.json")) == entry,
                "Standalone stage summary mismatch: " + stage)
        audit_name = stage.replace("-", "_").title() + "Audit.lean"
        log_name = stage + "-audit.log"
        require(entry["audit_source"] == audit_name and entry["audit_log"] == log_name,
                "Unexpected audit filenames: " + stage)
        audit_path = contained_file(evidence, audit_name)
        log_path = contained_file(evidence, log_name)
        require(digest(audit_path) == entry["audit_source_sha256"], "Audit source hash mismatch: " + stage)
        require(digest(log_path) == entry["audit_log_sha256"], "Audit log hash mismatch: " + stage)
        expected_audit = "import " + module + "\nset_option pp.universes false\n"
        expected_audit += "\n".join("#check @" + n + "\n#print axioms " + n for n in names) + "\n"
        require(audit_path.read_text() == expected_audit, "Audit source differs from exact current inventory: " + stage)
        log = log_path.read_text(encoding="utf-8")
        records = audit_records(log, names)
        require([m.group("name") for m in RECORD.finditer(ANSI.sub("", log))] == names,
                "Extra/out-of-order raw axiom record: " + stage)
        require(entry["targets"] == records, "Raw audits differ from summarized targets: " + stage)
        for kind, expected_log in (("build", stage + "-build.log"), ("audit", log_name)):
            matches = [(i, c) for i, c in enumerate(commands) if c["log"] == expected_log]
            require(len(matches) == 1, "Missing/duplicate " + kind + " command: " + stage)
            index, command_record = matches[0]
            command = command_record["command"]
            if kind == "build":
                require(command == ["lake", "build", module], "Wrong build command: " + stage)
            else:
                require(len(command) == 6 and command[:4] == ["lake", "env", "lean", "-R"]
                        and isinstance(command[-1], str)
                        and command[-1].replace("\\", "/").rsplit("/", 1)[-1] == audit_name,
                        "Wrong audit command: " + stage)
            contained_file(evidence, expected_log)
            stage_command_indices.append(index)
    require(stage_command_indices == sorted(stage_command_indices), "Compile/audit stage sequence mismatch")
    return {"status": "PASS_STANDARD_ONLY", "source_commit": source_commit,
            "compiler": version, "mathlib_commit": MATHLIB,
            "source_file_count": len(entries), "baseline_target_count": 401,
            "cutout_target_count": 85, "new_target_count": len(assembly_names),
            "target_count": len(all_names), "raw_named_audits_verified": True,
            "source_bytes_verified": True, "local_lean_executions": 0,
            "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", required=True, type=Path)
    parser.add_argument("--evidence-directory", required=True, type=Path)
    parser.add_argument("--source-commit")
    args = parser.parse_args()
    try:
        result = verify(args.repository_root.resolve(), args.evidence_directory.resolve(), args.source_commit)
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error), "local_lean_executions": 0}, ensure_ascii=False))
        return 1
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
