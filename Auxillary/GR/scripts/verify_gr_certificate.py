#!/usr/bin/env python3
"""Statically verify retained GR compiler evidence against exact source bytes.

No Lean/Lake/elan or network process is executed. This verifies a supplied
external certificate; it neither creates kernel evidence nor discharges the
explicit analytic/semantic hypotheses in the theorem statements.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
LEAN_COMMIT = "3447a668783dbce1a8fdb97101dd067687b2b418"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
STAGES = {"adapter": "GRAdapter", "forward": "NSEGRForward", "reverse": "NSEGRReverse"}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
SHA256 = re.compile(r"[a-f0-9]{64}\Z")
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
AXIOM = re.compile(r"['‘](?P<name>[^'’\r\n]+)['’]\s+"
                   r"(?:does not depend on any axioms|depends on axioms:\s*"
                   r"\[(?P<axioms>[^\]]*)\])", re.MULTILINE)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def ordinary_file(root: Path, relative: str) -> Path:
    pure = PurePosixPath(relative)
    require(bool(relative) and not pure.is_absolute() and str(pure) == relative
            and all(part not in {".", ".."} for part in pure.parts),
            "Invalid certificate path: " + relative)
    path = root.joinpath(*pure.parts)
    require(path.is_file() and not path.is_symlink(), "Missing ordinary file: " + str(path))
    require(path.resolve().is_relative_to(root.resolve()), "Escaping certificate path: " + relative)
    return path


def load_json(root: Path, relative: str) -> object:
    return json.loads(ordinary_file(root, relative).read_text(encoding="utf-8-sig"))


def compare_source(path: Path, relative: str, expected: str) -> dict:
    raw = path.read_bytes()
    actual = digest(raw)
    if actual == expected:
        return {"path": relative, "sha256": expected, "comparison": "EXACT_BYTES"}
    if relative == "GR_adapter/run.cmd":
        lf = raw.replace(b"\r\n", b"\n")
        require(b"\r" not in lf, "Bare CR in run.cmd; no newline adaptation permitted")
        for label, candidate in (("LF_BYTES_MATCH_CERTIFICATE", lf),
                                 ("CRLF_BYTES_MATCH_CERTIFICATE", lf.replace(b"\n", b"\r\n"))):
            if digest(candidate) == expected:
                return {"path": relative, "sha256": expected, "local_sha256": actual,
                        "comparison": label}
    raise ValueError("Source hash differs from certified input: " + relative)


def verify(artifact: Path, repo: Path, expected_sha: str, requested: list[str]) -> dict:
    require(re.fullmatch(r"[a-f0-9]{40}", expected_sha) is not None, "Exact source SHA required")
    require(isinstance(requested, list) and requested and
            all(isinstance(n, str) and NAME.fullmatch(n) for n in requested),
            "--targets-json must contain a nonempty array of declaration names")
    require(len(set(requested)) == len(requested), "Duplicate requested targets")
    summary = load_json(artifact, "audit-summary.json")
    provenance = load_json(artifact, "provenance-build.json")
    manifest = load_json(artifact, "source-manifest.json")
    for label, record in (("summary", summary), ("provenance", provenance), ("manifest", manifest)):
        require(isinstance(record, dict) and record.get("source_commit") == expected_sha,
                "Source commit mismatch in " + label)
    require(summary.get("status") == "PASS_STANDARD_ONLY" and
            provenance.get("status") == "PASS_STANDARD_ONLY", "External build/audit did not pass")
    require(summary.get("source_input_verification") == "PASS", "External source verification did not pass")
    require(summary.get("semantic_discharge") == "NOT_INFERRED_FROM_AXIOM_AUDIT",
            "Missing semantic-premise evidence boundary")
    require(set(summary.get("allowed_axioms", [])) == ALLOWED, "Axiom allowlist mismatch")
    require(provenance.get("requested_toolchain") == TOOLCHAIN, "Requested compiler mismatch")
    require(summary.get("actual_mathlib_commit") == MATHLIB and
            provenance.get("actual_mathlib_commit") == MATHLIB, "Mathlib pin mismatch")
    version = summary.get("actual_lean_version", "")
    require(isinstance(version, str) and version == provenance.get("actual_lean_version"),
            "Compiler version evidence disagrees")
    match = re.fullmatch(r"Lean \(version 4\.34\.0-rc1, ([^,\s]+), commit " + LEAN_COMMIT + r", Release\)", version)
    require(match is not None, "Exact Lean 4.34.0-rc1 release evidence missing")
    native_platform = provenance.get("external_platform")
    require(native_platform in {"linux", "windows"} and "-" + native_platform + "-" in match.group(1),
            "Native compiler platform mismatch")
    require(ordinary_file(artifact, "lean-version-build.log").read_text().strip() == version,
            "Raw compiler-version log disagrees")
    manifest_hash = digest(ordinary_file(artifact, "source-manifest.json").read_bytes())
    require(summary.get("source_manifest_sha256") == manifest_hash and
            provenance.get("source_manifest_sha256") == manifest_hash, "Source manifest hash mismatch")

    stages = summary.get("stages")
    require(isinstance(stages, list) and [s.get("stage") for s in stages] == list(STAGES),
            "Exact adapter/forward/reverse stage sequence required")
    certified: dict[str, dict] = {}
    inventory = load_json(repo, "Auxillary/GR/audit-targets.json")
    require(isinstance(inventory, dict) and set(inventory) == set(STAGES), "Source audit inventory mismatch")
    for stage in stages:
        key = stage["stage"]
        require(stage == load_json(artifact, key + "-summary.json"), "Combined/individual stage differs: " + key)
        require(stage.get("source_commit") == expected_sha and stage.get("status") == "PASS_STANDARD_ONLY"
                and stage.get("module") == STAGES[key], "Invalid stage certificate: " + key)
        require(provenance.get("stages", {}).get(key) == {"build": "PASS", "audit": "PASS_STANDARD_ONLY"},
                "Stage build/audit provenance did not pass: " + key)
        audit = ordinary_file(artifact, key.capitalize() + "Audit.lean")
        log_file = ordinary_file(artifact, key + "-audit.log")
        require(digest(audit.read_bytes()) == stage.get("audit_source_sha256") and
                digest(log_file.read_bytes()) == stage.get("audit_log_sha256"), "Raw audit hash differs: " + key)
        source = audit.read_text(encoding="utf-8-sig")
        require(re.search(r"^import " + STAGES[key] + r"$", source, re.M) is not None,
                "Audit does not import its exact stage module")
        targets = stage.get("targets")
        require(isinstance(targets, list) and targets, "Empty stage target certificate")
        names = [t.get("name") for t in targets]
        require(names == inventory[key] and len(set(names)) == len(names) and
                stage.get("target_count") == len(names), "Stage audit inventory/count differs: " + key)
        for pattern in (r"^#check @([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
                        r"^#print axioms ([A-Za-z_][A-Za-z0-9_'.]*)\s*$"):
            require(re.findall(pattern, source, re.M) == names, "Audit source target commands differ: " + key)
        log = ANSI.sub("", log_file.read_text(encoding="utf-8-sig"))
        require("sorryAx" not in log and not re.search(r"declaration uses ['‘]sorry", log)
                and not re.search(r"(?:^|\n).*:\s*error:", log), "Invalid raw audit log: " + key)
        raw: dict[str, list[set[str]]] = {}
        for record in AXIOM.finditer(log):
            axioms = set(filter(None, (x.strip() for x in (record.group("axioms") or "").split(","))))
            raw.setdefault(record.group("name"), []).append(axioms)
        for target in targets:
            name = target["name"]
            require(isinstance(name, str) and NAME.fullmatch(name) is not None and name not in certified,
                    "Invalid or duplicate global target")
            records = raw.get(name, [])
            require(len(records) == 1 and records[0] <= ALLOWED, "Missing/duplicate/unapproved raw axiom record: " + name)
            require(target.get("status") == "PASS_STANDARD_ONLY" and
                    set(target.get("axioms", [])) == records[0], "Axiom summary disagrees: " + name)
            certified[name] = {"name": name, "stage": key, "axioms": sorted(records[0])}
    require(summary.get("target_count") == len(certified), "Global target count differs")
    require(set(requested) <= certified.keys(), "Requested declarations absent: " + ", ".join(sorted(set(requested) - certified.keys())))

    inputs = manifest.get("files")
    require(isinstance(inputs, list) and inputs, "Empty source manifest")
    comparisons = []
    seen: set[str] = set()
    for entry in inputs:
        relative = entry.get("path")
        expected = entry.get("sha256")
        require(isinstance(relative, str) and relative not in seen and isinstance(expected, str)
                and SHA256.fullmatch(expected) is not None, "Invalid/duplicate source manifest item")
        seen.add(relative)
        comparisons.append(compare_source(ordinary_file(repo, relative), relative, expected))
    current_lean = {p.relative_to(repo).as_posix() for p in (repo / "GR_adapter").rglob("*.lean")
                    if ".lake" not in p.parts}
    required = {"GR_adapter/GRAdapter.lean", "GR_adapter/NSEGRForward.lean", "GR_adapter/NSEGRReverse.lean",
        "GR_adapter/lakefile.lean", "GR_adapter/lake-manifest.json", "GR_adapter/lean-toolchain",
        "GR_adapter/run.sh", "GR_adapter/run.cmd", "Auxillary/GR/scripts/run_gr.py",
        "Auxillary/GR/audit-targets.json", "Auxillary/GR/formalization-status.json"}
    require(required <= seen, "Manifest omits required entry/audit/config inputs: " + ", ".join(sorted(required - seen)))
    return {"status": "PASS_MATCHING_EXTERNAL_CERTIFICATE", "audited_source_commit": expected_sha,
        "native_platform": native_platform, "compiler": version, "mathlib": MATHLIB,
        "requested_target_count": len(requested), "certified_target_count": len(certified),
        "requested_targets": [certified[name] for name in requested],
        "source_manifest_sha256": manifest_hash, "source_input_count": len(comparisons),
        "newline_adaptations": [c for c in comparisons if c["comparison"] != "EXACT_BYTES"],
        "additional_unmanifested_lean_files": sorted(current_lean - seen),
        "additional_files_status": "NOT_CERTIFIED_BY_THIS_CERTIFICATE",
        "certificate_scope": "RECORDED_SOURCE_SNAPSHOT_AND_NAMED_TARGETS_ONLY",
        "semantic_premise_discharge": "NOT_INFERRED", "local_lean_execution": 0}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--expected-sha", required=True)
    parser.add_argument("--targets-json", type=Path, required=True)
    args = parser.parse_args()
    try:
        requested = json.loads(args.targets_json.read_text(encoding="utf-8-sig"))
        result = verify(args.artifact_dir.resolve(), args.repo_root.resolve(), args.expected_sha, requested)
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error), "local_lean_execution": 0}, indent=2))
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
