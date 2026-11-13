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
    TOOLCHAIN, audit_records, audit_source, digest, require,
    failed_assembly_modules, successful_dag_modules,
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
    certified = repo / "Auxillary/GR/Assembly/certified-base-targets.json"
    if certified.is_file():
        paths.add(certified)
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



def stage_layout(repo: Path, baseline: dict, cutout_names: list[str],
                 inventory: list[dict], individual: bool):
    """Reconstruct the runner's full deterministic stage inventory from source."""
    stages = [(label, module, baseline[label]) for label, module in
              (("adapter", "GRAdapter"), ("forward", "NSEGRForward"), ("reverse", "NSEGRReverse"))]
    stages.append(("cutouts", "TempEndpoints", cutout_names))
    direct = {}

    def dependencies(module):
        if module not in direct:
            source = repo / "ASSEMBLY" / (module.replace(".", "/") + ".lean")
            direct[module] = set(re.findall(r"^import\s+(GRAssembly(?:\.\S+)?)\s*$",
                source.read_text(), re.MULTILINE)) if source.is_file() else set()
        return direct[module]

    ordered, visiting, visited = [], set(), set()
    selected = {x["module"] for x in inventory}

    def visit(module):
        if module in visited:
            return
        require(module not in visiting, "Cyclic assembly imports: " + module)
        visiting.add(module)
        for dependency in sorted(dependencies(module)):
            visit(dependency)
        visiting.remove(module)
        visited.add(module)
        if module in selected:
            ordered.append(module)

    for module in sorted(selected):
        visit(module)

    def closure(module, seen=None):
        seen = set() if seen is None else seen
        for dependency in dependencies(module):
            if dependency not in seen:
                seen.add(dependency)
                closure(dependency, seen)
        return seen

    if individual:
        certified = read_json(repo / "Auxillary/GR/Assembly/certified-base-targets.json")
        require(isinstance(certified, list) and len(certified) == len(set(certified)),
                "Malformed certified-base inventory")
        require(set(certified) <= {x["name"] for x in inventory}, "Unknown certified-base target")
        base = [x["name"] for x in inventory if x["name"] in certified]
        if base:
            stages.append(("assembly-certified-base", "GRAssembly.CertifiedBase", base))
        for number, module in enumerate(ordered, 1):
            names = [x["name"] for x in inventory if x["module"] == module and x["name"] not in certified]
            if names:
                stages.append((f"assembly-{number:03d}", module, names))
    else:
        stages.append(("assembly", "GRAssembly", [x["name"] for x in inventory]))
    return stages, {module: closure(module) for _, module, _ in stages}


def verify_stages(repo: Path, evidence: Path, summary: dict, provenance: dict,
                  baseline: dict, cutout_names: list[str], inventory: list[dict],
                  source_commit: str) -> dict:
    """Verify complete stage partition and fresh build/audit evidence, including batches."""
    passed, failed = summary["stages"], summary.get("failed_stages", [])
    require(isinstance(passed, list) and isinstance(failed, list), "Malformed stage lists")
    require(provenance["stages"] == passed and provenance.get("failed_stages", []) == failed,
            "Provenance and summary stages disagree")
    require(all(isinstance(x, dict) for x in passed + failed), "Malformed stage entry")
    identifiers = [x["stage"] for x in passed + failed]
    require(len(set(identifiers)) == len(identifiers), "Duplicate or overlapping stage outcome")
    stages, closures = stage_layout(repo, baseline, cutout_names, inventory, "assembly" not in identifiers)
    expected = {stage: (module, names) for stage, module, names in stages}
    require(set(identifiers) == set(expected), "Incomplete stage partition")
    require([x["stage"] for x in passed] == [stage for stage, _, _ in stages if stage in {x["stage"] for x in passed}],
            "Successful stage order mismatch")
    require(summary["status"] == ("PARTIAL_STANDARD_ONLY" if failed else "PASS_STANDARD_ONLY"),
            "Stage failures and overall status disagree")
    total = sum(len(names) for _, _, names in stages)
    audited = sum(len(expected[x["stage"]][1]) for x in passed)
    require(type(summary["target_count"]) is int and summary["target_count"] == audited,
            "Audited target count mismatch")
    commands = provenance["commands"]
    require(isinstance(commands, list) and bool(commands), "Missing command provenance")
    logs = {}
    for index, command in enumerate(commands):
        require(isinstance(command, dict) and type(command.get("exit_code")) is int
                and isinstance(command.get("command"), list) and bool(command["command"])
                and all(isinstance(arg, str) for arg in command["command"])
                and isinstance(command.get("log"), str), "Malformed command provenance")
        require(command["log"] not in logs, "Duplicate command log")
        contained_file(evidence, command["log"])
        logs[command["log"]] = (index, command)
        if command["exit_code"]:
            require(command["command"][:2] == ["lake", "build"] or
                    (command["command"][:4] == ["lake", "env", "lean", "-R"]
                     and command["log"].endswith("-audit.log")), "Unrelated failed provenance command")
    modules = {module for _, module, _ in stages}
    explicit_failures, successful_builds = set(), {module: [] for module in modules}
    for index, command in enumerate(commands):
        args = command["command"]
        if args[:2] != ["lake", "build"]:
            continue
        targets = args[2:]
        require(bool(targets) and len(targets) == len(set(targets)) and set(targets) <= modules,
                "Unexpected build targets")
        if command["exit_code"] == 0:
            successes = set(targets)
        elif command["log"] == "dag-build.log":
            text = contained_file(evidence, command["log"]).read_text()
            explicit_failures |= failed_assembly_modules(text, modules)
            successes = successful_dag_modules(text, set(targets))
        else:
            successes = set()
        for module in successes:
            successful_builds[module].append(index)
    outcomes = {x["stage"]: x for x in passed + failed}
    failed_modules = set()
    for stage, module, _ in stages:
        entry = outcomes[stage]
        require(entry["module"] == module, "Stage module mismatch: " + stage)
        require(read_json(contained_file(evidence, stage + "-summary.json")) == entry,
                "Standalone stage summary mismatch: " + stage)
        if entry in failed:
            require(entry["status"] in {"FAIL", "BLOCKED_BY_FAILED_DEPENDENCY"}, "Invalid failure status")
            if entry["status"] == "BLOCKED_BY_FAILED_DEPENDENCY":
                dependencies = entry.get("dependencies", [])
                require(isinstance(dependencies, list) and bool(dependencies)
                        and len(set(dependencies)) == len(dependencies)
                        and set(dependencies) <= (closures[module] & failed_modules),
                        "Unsupported blocked stage: " + stage)
            else:
                own_failure = any(c["exit_code"] != 0 for _, c in
                    [logs[name] for name in (stage + "-build.log", stage + "-audit.log") if name in logs])
                # An exit-zero audit can still fail the exact named/approved-axiom gate.
                invalid_audit = False
                if stage + "-audit.log" in logs:
                    try:
                        audit_records(contained_file(evidence, stage + "-audit.log").read_text(), expected[stage][1])
                    except ValueError:
                        invalid_audit = True
                require(module in explicit_failures or own_failure or invalid_audit,
                        "Unsupported failed stage: " + stage)
            failed_modules.add(module)
    batch_entries = [entry for entry in passed if entry.get("audit_mode") == "FRESH_BATCH"]
    require(not batch_entries or len(batch_entries) == len(passed), "Mixed batch/stage promotion")
    batch_stages = [(entry["stage"], entry["module"], expected[entry["stage"]][1]) for entry in batch_entries]
    checked_audits = {}
    audit_indices = []
    for entry in passed:
        stage = entry["stage"]
        module, names = expected[stage]
        require(entry["status"] == "PASS_STANDARD_ONLY" and entry["source_commit"] == source_commit,
                "Unsuccessful/mismatched stage: " + stage)
        require(type(entry["target_count"]) is int and entry["target_count"] == len(names), "Stage target count mismatch")
        require(module not in explicit_failures and not closures[module] & failed_modules,
                "Failed module or dependency entered successful audit: " + module)
        batched = entry.get("audit_mode") == "FRESH_BATCH"
        audit_name = "BatchAudit.lean" if batched else stage.replace("-", "_").title() + "Audit.lean"
        log_name = "batch-audit.log" if batched else stage + "-audit.log"
        require(entry["audit_source"] == audit_name and entry["audit_log"] == log_name, "Unexpected audit filenames")
        audit_path, log_path = contained_file(evidence, audit_name), contained_file(evidence, log_name)
        require(digest(audit_path) == entry["audit_source_sha256"], "Audit source hash mismatch")
        require(digest(log_path) == entry["audit_log_sha256"], "Audit log hash mismatch")
        if audit_name not in checked_audits:
            expected_source, audit_names = audit_source(batch_stages if batched else [(stage, module, names)])
            require(audit_path.read_text() == expected_source, "Audit source differs from exact current inventory")
            text = log_path.read_text()
            records = audit_records(text, audit_names)
            require([m.group("name") for m in RECORD.finditer(ANSI.sub("", text))] == audit_names,
                    "Extra/out-of-order raw axiom record")
            require(log_name in logs, "Missing audit command")
            index, command = logs[log_name]
            args = command["command"]
            require(command["exit_code"] == 0 and len(args) == 6
                    and args[:4] == ["lake", "env", "lean", "-R"]
                    and args[-1].replace("\\", "/") == args[-2].replace("\\", "/").rstrip("/") + "/" + audit_name,
                    "Unsuccessful or wrong fresh audit command")
            checked_audits[audit_name] = (index, {record["name"]: record for record in records})
        index, records = checked_audits[audit_name]
        require(any(build_index < index for build_index in successful_builds[module]),
                "No current successful build before audit: " + module)
        require(entry["targets"] == [records[name] for name in names], "Raw audits differ from summarized targets")
        audit_indices.append(index)
    require(audit_indices == sorted(audit_indices), "Audit stage sequence mismatch")
    return {"target_count": audited, "expected_target_count": total,
            "unresolved_target_count": total - audited, "failed_stage_count": len(failed)}

def verify(repo: Path, evidence: Path, requested_commit: str | None,
           allow_partial: bool = False) -> dict:
    require(repo.is_dir() and evidence.is_dir(), "Repository and evidence directories must exist")
    summary = read_json(contained_file(evidence, "audit-summary.json"))
    require(isinstance(summary, dict), "Malformed audit summary")
    require(summary["schema_version"] == 1, "Unsupported audit-summary schema")
    allowed_statuses = {"PASS_STANDARD_ONLY"}
    if allow_partial:
        allowed_statuses.add("PARTIAL_STANDARD_ONLY")
    require(summary["status"] in allowed_statuses, "Assembly audit did not pass; partial evidence requires --allow-partial")
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
                       ("new_target_count", len(assembly_names))):
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
    require(provenance["status"] == summary["status"], "Build provenance status mismatch")
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

    stage_result = verify_stages(repo, evidence, summary, provenance, baseline, cutout_names,
                                 inventory, source_commit)
    return {"status": summary["status"], "source_commit": source_commit,
            "compiler": version, "mathlib_commit": MATHLIB,
            "source_file_count": len(entries), "baseline_target_count": 401,
            "cutout_target_count": 85, "new_target_count": len(assembly_names),
            **stage_result, "raw_named_audits_verified": True,
            "source_bytes_verified": True, "local_lean_executions": 0,
            "root_promotion": "NOT_INFERRED_FROM_EVIDENCE_VERIFICATION",
            "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", required=True, type=Path)
    parser.add_argument("--evidence-directory", required=True, type=Path)
    parser.add_argument("--source-commit")
    parser.add_argument("--allow-partial", action="store_true",
                        help="Verify complete partial evidence without promoting unresolved targets")
    args = parser.parse_args()
    try:
        result = verify(args.repository_root.resolve(), args.evidence_directory.resolve(),
                        args.source_commit, args.allow_partial)
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error), "local_lean_executions": 0}, ensure_ascii=False))
        return 1
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
