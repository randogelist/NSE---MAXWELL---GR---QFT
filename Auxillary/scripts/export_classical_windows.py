#!/usr/bin/env python3
"""Export byte-identical native Lean sources to a Windows-safe cached package.

Only source/Git/file operations occur. This exporter never runs Lean, Lake or elan.
The canonical arrow-directory layout and every proof body remain unchanged.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOTS = {
    "ClassicalMechanics": "Classical_Mechanics_adapter",
    "ClassicalMechanicsForward": "B <-> ClassicalMechanics/=>",
    "ClassicalMechanicsReverse": "B <-> ClassicalMechanics/<=",
    "NSEMaxwell": "Fefferman_adapter",
    "NSEMaxwellForward": "B <-> Maxwell/=>",
    "NSEMaxwellReverse": "B <-> Maxwell/<=",
    "MaxwellEndpoint": "Maxwell_Endpoint",
    "SingularClosure": "Fefferman_adapter/NativeSources/methlib",
    "MethlibEndpoints": "Fefferman_adapter",
}
EXTERNAL = {"Mathlib", "Batteries", "Lean", "Init", "Std", "Aesop", "Qq", "ImportGraph", "ProofWidgets", "LeanSearchClient", "Plausible"}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def export(root: Path, destination: Path) -> dict:
    if destination.exists():
        raise ValueError("A new destination is required; existing source and caches are preserved.")
    root = root.resolve()
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                            check=True, capture_output=True, text=True).stdout.strip()
    files: dict[str, bytes] = {}
    source_map: list[dict] = []

    def copy(source: str, target: str) -> None:
        data = (root / source).read_bytes()
        committed = subprocess.run(["git", "show", f"{commit}:{source}"], cwd=root,
                                   check=True, capture_output=True).stdout
        if data != committed:
            raise ValueError(f"Uncommitted or byte-different source: {source}")
        files[target] = data
        source_map.append({"source": source, "path": target, "sha256": digest(data)})

    seen: set[str] = set()
    active: set[str] = set()
    modules: list[str] = []

    def visit(module: str) -> None:
        if not MODULE.fullmatch(module):
            raise ValueError(f"Invalid module: {module}")
        prefix = module.split(".", 1)[0]
        if prefix in EXTERNAL:
            return
        if prefix not in ROOTS:
            raise ValueError(f"Unregistered import: {module}")
        if module in active:
            raise ValueError(f"Cyclic module import: {module}")
        if module in seen:
            return
        active.add(module)
        relative = module.replace(".", "/") + ".lean"
        source = ROOTS[prefix] + "/" + relative
        copy(source, relative)
        for line in files[relative].decode("utf-8-sig").splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                for imported in match.group(1).split("--", 1)[0].split():
                    visit(imported)
        active.remove(module)
        seen.add(module)
        if module != "ClassicalMechanics.Audit":
            modules.append(module)

    visit("ClassicalMechanics.Audit")
    visit("ClassicalMechanics")
    copy("lean-toolchain", "lean-toolchain")
    copy("lake-manifest.json", "lake-manifest.json")
    copy("Auxillary/classical-mechanics-audit-targets.txt", "audit-targets.txt")
    copy("Auxillary/classical-mechanics-status.json", "formalization-status.json")
    copy("Auxillary/scripts/verify_audit.py", "audit_parser.py")
    copy("Auxillary/scripts/classical_windows_run.py", "run.py")
    libraries = sorted({m.split(".", 1)[0] for m in seen})
    files["lakefile.lean"] = ('''import Lake
open Lake DSL
package nse_maxwell where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
''' + "\n".join(f"lean_lib {name}" for name in libraries) + "\n").encode()
    files["run.cmd"] = b'''@echo off\r
setlocal\r
cd /d "%~dp0"\r
where py >nul 2>nul\r
if errorlevel 1 (\r
  python run.py --external-native-windows %*\r
) else (\r
  py -3 run.py --external-native-windows %*\r
)\r
exit /b %errorlevel%\r
'''
    files["build-targets.json"] = (json.dumps(modules, indent=2) + "\n").encode()
    files["README.txt"] = b'''EXTERNAL NATIVE WINDOWS LEAN 4.34.0-rc1
Run run.cmd from an existing native Windows toolchain environment.
Prerequisites: Python >=3.9, Git, native Lean/Lake 4.34.0-rc1.
The first run obtains the pinned dependencies and official Mathlib cache.
All subsequent runs preserve .lake, compiler and Mathlib download caches.
Lean source bytes are identical to the exact source commit in source-map.json.
Only source paths and Lake library roots are remapped for Windows filenames.
No authoring-time Lean execution is performed by the exporter.
Fresh external evidence is written under artifacts/windows/.
An axiom audit does not discharge theorem hypotheses or semantic premises.
'''
    source_info = {"schema_version": 1, "source_commit": commit,
                   "proof_bodies_byte_identical": True,
                   "local_lean_executions": 0,
                   "source_map": sorted(source_map, key=lambda item: item["path"])}
    files["source-map.json"] = (json.dumps(source_info, indent=2) + "\n").encode()
    manifest = {"schema_version": 1, "source_commit": commit,
                "files": [{"path": name, "sha256": digest(data)} for name, data in sorted(files.items())]}
    files["source-manifest.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    destination.mkdir(parents=True)
    for name, data in files.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return {"status": "EXPORTED_SOURCE_ONLY", "source_commit": commit,
            "destination": str(destination), "native_modules": len(modules),
            "files": len(files), "local_lean_executions": 0,
            "source_manifest_sha256": digest(files["source-manifest.json"])}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(export(args.repo_root, args.destination.resolve()), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
