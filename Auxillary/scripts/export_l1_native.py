#!/usr/bin/env python3
"""Export the exact native L1 import closure without executing Lean/Lake/elan.

Only committed source bytes are accepted. The output is a new, Windows-safe
source package; existing releases, dependency checkouts and caches are untouched.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

from export_classical_windows import EXTERNAL, MODULE, ROOTS, digest


ROOT_MODULE = "ClassicalMechanicsAssembly.FlowRealization"
TARGETS = (
    "ClassicalMechanicsAssembly.jointFlowRegularity_of_smooth_periodic",
    "ClassicalMechanicsAssembly.L1_native",
    "ClassicalMechanicsAssembly.CLASSICAL_MECHANICS_MATERIAL_NATIVE",
)
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
LOCAL_ROOTS = {**ROOTS, "ClassicalMechanicsAssembly": "ASSEMBLY"}


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2) + "\n").encode()


def export(root: Path, destination: Path, *, check_only: bool = False) -> dict:
    root, destination = root.resolve(), destination.resolve()
    if destination.exists():
        raise ValueError("A new destination is required; existing sources and caches are preserved.")
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, check=True,
                            capture_output=True, text=True).stdout.strip()
    files: dict[str, bytes] = {}
    source_map: list[dict] = []

    def copy(source: str, target: str) -> None:
        data = (root / source).read_bytes()
        committed = subprocess.run(["git", "show", f"{commit}:{source}"], cwd=root,
                                   check=True, capture_output=True).stdout
        if data != committed:
            raise ValueError(f"Uncommitted or byte-different export input: {source}")
        if target in files:
            raise ValueError(f"Duplicate export path: {target}")
        files[target] = data
        source_map.append({"source": source, "path": target, "sha256": digest(data)})

    seen: set[str] = set()
    active: set[str] = set()
    external: set[str] = set()
    modules: list[str] = []

    def visit(module: str) -> None:
        if not MODULE.fullmatch(module):
            raise ValueError(f"Invalid module: {module}")
        prefix = module.split(".", 1)[0]
        if prefix in EXTERNAL:
            external.add(module)
            return
        if prefix not in LOCAL_ROOTS:
            raise ValueError(f"Unregistered import: {module}")
        if module in active:
            raise ValueError(f"Cyclic import: {module}")
        if module in seen:
            return
        if module.startswith("ClassicalMechanicsAssembly.Literature"):
            raise ValueError(f"Literature input is outside the native export: {module}")
        active.add(module)
        target = module.replace(".", "/") + ".lean"
        copy(LOCAL_ROOTS[prefix] + "/" + target, target)
        for line in files[target].decode("utf-8-sig").splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                for imported in match.group(1).split("--", 1)[0].split():
                    visit(imported)
        active.remove(module)
        seen.add(module)
        modules.append(module)

    visit(ROOT_MODULE)
    copy("lean-toolchain", "lean-toolchain")
    copy("lake-manifest.json", "lake-manifest.json")
    copy("Auxillary/scripts/verify_audit.py", "audit_parser.py")
    copy("Auxillary/scripts/l1_native_windows_run.py", "run.py")
    copy("Auxillary/assembly/L1_FLOW_REALIZATION_A_TIER.txt", "L1_native_A_TIER.txt")
    copy("Auxillary/scripts/l1_native_run.cmd", "run.cmd")
    # Batch-file line endings are packaging metadata; Lean source bytes are never rewritten.
    command_source_hash = source_map[-1]["sha256"]
    files["run.cmd"] = files["run.cmd"].replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
    source_map[-1].update(source_sha256=command_source_hash,
                         sha256=digest(files["run.cmd"]), transform="CRLF_BATCH_FILE")
    if files["lean-toolchain"].decode().strip() != TOOLCHAIN:
        raise ValueError("Unexpected Lean toolchain pin.")
    lock = json.loads(files["lake-manifest.json"])
    if not any(p["name"] == "mathlib" and p["rev"] == MATHLIB for p in lock["packages"]):
        raise ValueError("Unexpected Mathlib revision pin.")
    libraries = sorted({module.split(".", 1)[0] for module in modules})
    files["lakefile.lean"] = ('''import Lake
open Lake DSL
package nse_maxwell where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "''' + MATHLIB + '"\n' + "\n".join(f"lean_lib {name}" for name in libraries) + "\n").encode()
    files["L1_native.lean"] = (
        f"import {ROOT_MODULE}\n\nset_option pp.universes true\n\n" +
        "\n".join(f"#check @{name}\n#print axioms {name}" for name in TARGETS) + "\n").encode()
    files["audit-targets.txt"] = ("\n".join(TARGETS) + "\n").encode()
    files["build-targets.json"] = json_bytes(modules)
    files["cache-targets.json"] = json_bytes(sorted(
        name for name in external if name == "Mathlib" or name.startswith("Mathlib.")))
    files["formalization-scope.json"] = json_bytes({
        "export_status": "EXPORTED_SOURCE_ONLY",
        "theorem_status_record": "L1_native_A_TIER.txt",
        "portable_windows_validation": "REQUIRES_MATCHING_EXTERNAL_RUN",
        "root_module": ROOT_MODULE, "root_targets": TARGETS,
        "flow_scope": "For T>0 and a supplied smooth periodic divergence-free velocity on [0,T], construct a normalized smooth material path and inverse realizing its ODE.",
        "equation_scope": "For the same velocity and a supplied smooth pressure, the exact Eulerian and pulled-back material equations are equivalent; viscosity is arbitrary.",
        "excluded_claims": ["Arbitrary-data NSE existence", "Global-in-time NSE regularity",
                            "Full moving-region balance", "Solution-set bijection"],
        "approved_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "analytic_premise_discharge": "Not inferred from an axiom audit.",
    })
    files["README.txt"] = b'''EXACT NATIVE L1 SOURCE EXPORT
Entry: L1_native.lean. Definitions and theorem bodies remain in their original modules.
Exact source status: L1_native_A_TIER.txt; export alone never promotes that status.
Source identity: source-map.json; complete export hashes: source-manifest.json.
External prerequisites: native Windows Lean/Lake 4.34.0-rc1, Git, Python >=3.10.
Command: run.cmd
Existing .lake objects and download caches are preserved and checked incrementally.
Missing pinned dependencies and official Mathlib cache entries are fetched normally.
No clean, forced cache replacement, lake update, or local authoring-time Lean execution.
Every run creates a separate artifacts/windows/<run-id>/ evidence directory.
Compilation is followed by a fresh root signature and standard-only axiom audit.
Source export alone does not establish A_TIER; review exact premises separately.
'''
    files["source-map.json"] = json_bytes({
        "schema_version": 1, "source_commit": commit, "root_module": ROOT_MODULE,
        "proof_bodies_byte_identical": True, "local_lean_executions": 0,
        "source_map": sorted(source_map, key=lambda item: item["path"]),
    })
    files["source-manifest.json"] = json_bytes({
        "schema_version": 1, "source_commit": commit,
        "files": [{"path": name, "sha256": digest(data)} for name, data in sorted(files.items())],
    })
    if not check_only:
        destination.mkdir(parents=True)
        for name, data in files.items():
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    return {"status": "CHECKED_SOURCE_ONLY" if check_only else "EXPORTED_SOURCE_ONLY",
            "source_commit": commit, "destination": str(destination),
            "native_modules": len(modules), "files": len(files),
            "root_targets": TARGETS, "local_lean_executions": 0,
            "source_manifest_sha256": digest(files["source-manifest.json"])}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(export(args.repo_root, args.destination, check_only=args.check_only), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
