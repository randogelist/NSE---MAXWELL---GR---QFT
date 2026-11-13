#!/usr/bin/env python3
"""External native Windows replay, pinned official caches, and exact theorem audit."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time
from windows_layout import checkout_for_bundle, git, layout

TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
MATHLIB = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[3])
    args = p.parse_args()
    if platform.system() != "Windows":
        raise RuntimeError("EXTERNAL_NATIVE_WINDOWS_REQUIRED")
    root = args.repo_root.resolve()
    if not (root / ".git").exists():
        root = checkout_for_bundle(root)
    commit = git(root, "rev-parse", "HEAD").decode().strip()
    mapped = layout(root, commit, create=True)
    report = root / "artifacts/external-windows"
    report.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, MATHLIB_NO_CACHE_ON_UPDATE="1",
               NSE_QUANTUM_OBLIGATIONS_EXTERNAL_NATIVE="1", PYTHONUTF8="1")
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    timings = []

    def run(argv, filename):
        if argv[0] == "lake":
            argv = ["lake", "--file", mapped["effective_config_path"], *argv[1:]]
        print("+ " + " ".join(map(str, argv)), flush=True)
        start = time.monotonic()
        r = subprocess.run(list(map(str, argv)), cwd=root, env=env, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        output = r.stdout + r.stderr
        (report / filename).write_text(output, encoding="utf-8")
        print(output, flush=True)
        timings.append({"argv": list(map(str, argv)), "exit_code": r.returncode,
                        "elapsed_seconds": round(time.monotonic() - start, 3), "log": filename})
        (report / "windows-command-timings.json").write_text(json.dumps(timings, indent=2) + "\n")
        if r.returncode:
            raise RuntimeError(f"External command failed ({r.returncode}): {filename}")
        return output.strip()

    def sha(path):
        return hashlib.sha256((root / path).read_bytes()).hexdigest()

    if (root / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
        raise RuntimeError("Compiler pin differs")
    version_output = run(["lean", "--version"], "lean-version.log")
    versions = [s for s in version_output.splitlines() if s.startswith("Lean (version ")]
    if len(versions) != 1 or not re.search(r"version 4\.34\.0-rc1,\s*[^,\s]*-windows-", versions[0]):
        raise RuntimeError("Matching native Windows Lean 4.34.0-rc1 required")
    version = versions[0]
    lock_hash = sha("lake-manifest.json")
    lock = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    pins = lock["packages"]
    if {x["name"]: x["rev"] for x in pins}.get("mathlib") != MATHLIB:
        raise RuntimeError("Mathlib pin differs")
    # Lake resolves the existing lock only; no lake update or source rewrite.
    run(["lake", "env", "lean", "--version"], "dependency-resolution.log")
    revisions = []
    for item in pins:
        name = item["name"]
        if not re.fullmatch(r"[A-Za-z0-9_-]+", name) or item["type"] != "git":
            raise RuntimeError("Unsupported dependency")
        path = ".lake/packages/" + name
        revision = run(["git", "-C", path, "rev-parse", "HEAD"], "dependency-" + name + ".log")
        if revision != item["rev"]:
            raise RuntimeError("Dependency revision differs: " + name)
        if run(["git", "-C", path, "status", "--porcelain", "--untracked-files=no"],
               "dependency-" + name + "-status.log"):
            raise RuntimeError("Tracked dependency modifications: " + name)
        revisions.append({"name": name, "revision": revision})
    for package in ("Fefferman_adapter", "Maxwell_Endpoint"):
        run([sys.executable, package + "/scripts/verify_native_sources.py", "--package-root", package,
             "--dependency-root", ".lake/packages", "--report", report / (package + "-sources.json")],
            package + "-sources.log")
    targets = sorted({s.strip() for s in (root / "Auxillary/cache-targets.txt").read_text(encoding="utf-8").splitlines()
                      if s.strip() and not s.lstrip().startswith("#")})
    if not targets or any(not re.fullmatch(r"Mathlib(?:\.[A-Za-z0-9_]+)*", s) for s in targets):
        raise RuntimeError("Invalid Mathlib cache targets")
    run(["lake", "exe", "cache", "get", "--cache-from=master,legacy", *targets], "official-cache.log")
    for target in targets:
        if not (root / ".lake/packages/mathlib/.lake/build/lib/lean" / (target.replace(".", "/") + ".olean")).is_file():
            raise RuntimeError("Missing official cached module: " + target)
    if sha("lake-manifest.json") != lock_hash:
        raise RuntimeError("Dependency preparation modified the source lock")
    inputs = ["platform=windows", "toolchain=" + TOOLCHAIN, "compiler=" + version]
    inputs += [n + "=" + sha(n) for n in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")]
    inputs.append("targets=" + ",".join(targets))
    inputs += ["windows_effective_config=" + mapped["effective_config_sha256"],
               "windows_layout=" + sha("artifacts/external-windows/source-layout.json")]
    prep = {"schema_version": 1, "status": "PASS", "external_platform": "windows",
            "dependency_fingerprint": hashlib.sha256("\n".join(inputs).encode()).hexdigest(),
            "dependency_inputs": inputs, "cache_targets": targets, "dependency_revisions": revisions,
            "proof_or_audit_reuse": False}
    preparation = report / "dependency-preparation.json"
    preparation.write_text(json.dumps(prep, indent=2) + "\n", encoding="utf-8")
    return subprocess.run([sys.executable, str(root / "Auxillary/quantum/obligations/run.py"),
                           "--repo-root", str(root), "--expected-platform", "windows", "--source-commit", commit,
                           "--dependency-report", str(preparation),
                           "--report-directory", str(report / "quantum-obligations")],
                          cwd=root, env=env).returncode

if __name__ == "__main__":
    raise SystemExit(main())
