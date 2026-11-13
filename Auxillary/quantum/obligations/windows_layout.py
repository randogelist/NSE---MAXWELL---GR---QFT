"""Materialize exact Git blobs under Windows-safe source roots; no Lean execution."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPOSITORY = "https://github.com/randogelist/NSE---MAXWELL---GR---QFT.git"
ROOTS = {"B <-> Maxwell/=>": "NSEMaxwellForward", "B <-> Maxwell/<=": "NSEMaxwellReverse",
         "B <-> Quantum/=>": "NSEQuantumForward", "B <-> Quantum/<=": "NSEQuantumReverse"}

def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def blob_hash(raw):
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()

def layout(root, commit, create=False):
    root = Path(root).resolve()
    if not re.fullmatch(r"[a-f0-9]{40}", commit):
        raise ValueError("Invalid immutable source commit")
    inventory = {}
    for row in git(root, "ls-tree", "-rz", "--full-tree", commit).split(b"\0"):
        if row:
            header, name = row.split(b"\t", 1)
            mode, kind, oid = header.decode().split()
            if kind == "blob": inventory[name.decode()] = (mode, oid)
    original = (root / "lakefile.lean").read_bytes()
    if blob_hash(original) != inventory["lakefile.lean"][1]:
        raise ValueError("Original Lake configuration differs from Git")
    prefix = "artifacts/external-windows/source-layout/" + commit
    effective = original.decode("utf-8")
    entries = []
    for source_root, safe_root in ROOTS.items():
        target_root = prefix + "/" + safe_root
        quoted = '"' + source_root + '"'
        if effective.count(quoted) != 1:
            raise ValueError("Expected exactly one source root in Lake configuration: " + source_root)
        effective = effective.replace(quoted, '"' + target_root + '"')
        selected = [(p, mode, oid) for p, (mode, oid) in inventory.items() if p.startswith(source_root + "/")]
        if not selected: raise ValueError("Missing original source root: " + source_root)
        for original_path, mode, oid in sorted(selected):
            if mode not in {"100644", "100755"}: raise ValueError("Unsupported staged Git mode")
            mapped = target_root + original_path[len(source_root):]
            raw = git(root, "cat-file", "blob", oid)
            if blob_hash(raw) != oid: raise ValueError("Git blob identity mismatch")
            target = root / mapped
            if not target.resolve().is_relative_to(root): raise ValueError("Escaping source map")
            if create and not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            if not target.is_file() or target.read_bytes() != raw:
                raise ValueError("Mapped source differs from immutable Git blob: " + original_path)
            entries.append({"original_path": original_path, "mapped_path": mapped,
                            "git_blob_sha": oid, "sha256": digest(raw)})
    config_path = "artifacts/external-windows/lakefile_windows.lean"
    config_raw = effective.encode("utf-8")
    if create:
        (root / config_path).parent.mkdir(parents=True, exist_ok=True)
        (root / config_path).write_bytes(config_raw)
    if (root / config_path).read_bytes() != config_raw:
        raise ValueError("Windows Lake configuration is not the exact four-path transformation")
    record = {"schema_version": 1, "source_commit": commit, "original_config_sha256": digest(original),
              "effective_config_path": config_path, "effective_config_sha256": digest(config_raw),
              "theorem_source_modifications": [], "files": entries}
    manifest_path = root / "artifacts/external-windows/source-layout.json"
    if create:
        manifest_path.write_bytes((json.dumps(record, indent=2) + "\n").encode())
    elif json.loads(manifest_path.read_text(encoding="utf-8")) != record:
        raise ValueError("Windows layout manifest differs from verified Git source mapping")
    return record

def checkout_for_bundle(bundle_root):
    """An immutable companion pin enables standalone ZIP replay with Git installed."""
    bundle_root = Path(bundle_root).resolve()
    pin_path = bundle_root / "Auxillary/quantum/obligations/replay-source.json"
    if not pin_path.is_file():
        raise ValueError("No exact Git checkout or companion replay-source.json; use --repo-root")
    pin = json.loads(pin_path.read_text(encoding="utf-8"))
    commit = pin.get("source_commit", "")
    if pin.get("repository") != REPOSITORY or not re.fullmatch(r"[a-f0-9]{40}", commit):
        raise ValueError("Invalid immutable replay pin")
    target = bundle_root / "replay-checkout"
    if target.exists():
        if git(target, "rev-parse", "HEAD").decode().strip() != commit:
            raise ValueError("Existing replay checkout has another commit")
        return target
    subprocess.run(["git", "init", str(target)], check=True)
    git(target, "remote", "add", "origin", REPOSITORY)
    git(target, "config", "core.autocrlf", "false")
    git(target, "config", "core.longpaths", "true")
    git(target, "fetch", "--depth=1", "origin", commit)
    git(target, "sparse-checkout", "init", "--no-cone")
    git(target, "sparse-checkout", "set", "/lean-toolchain", "/lakefile.lean", "/lake-manifest.json",
        "/.gitattributes", "/.github/", "/Auxillary/", "/Quantum_adapter/", "/Fefferman_adapter/", "/Maxwell_Endpoint/")
    git(target, "checkout", "--detach", "FETCH_HEAD")
    if git(target, "rev-parse", "HEAD").decode().strip() != commit:
        raise ValueError("Fetched source commit mismatch")
    return target
