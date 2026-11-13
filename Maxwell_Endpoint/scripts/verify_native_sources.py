#!/usr/bin/env python3
"""Verify package-owned source snapshots and their reachable Lean import closure.

This program never executes Lean, Lake or elan. Full verification checks the
existing dependency cache; --source-only checks source materialization only.
"""

from __future__ import annotations

import argparse
import base64
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
from typing import Any


TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
METHLIB_REVISION = "e9cf90726b8544a268469ebc8fa6634e9c713e07"
COMPILER_ROOTS = {"Init", "Lean", "Std", "Lake"}
IMPORT_MODIFIERS = {"all", "public", "private", "meta"}
SHA1 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
ENDPOINT_NAMES = [
    "SingularClosure.torusDatumComponent_fourierCoeff",
    "SingularClosure.datumFourierCoeff_coordinateDerivative",
    "SingularClosure.FOURIER_POLYNOMIAL_DECAY",
    "SingularClosure.scalarFourierSeries_contDiff",
    "SingularClosure.scalarFourierSeries_coefficient",
    "SingularClosure.datumFourierCoeff_injective_continuous_periodic",
    "SingularClosure.infiniteTransportPressure_recovery",
    "SingularClosure.datumFourierCoeff_smoothFourierSynthesis",
    "SingularClosure.smoothFourierSynthesis_coordinateDerivative",
    "SingularClosure.summable_torusSobolevWeight_inv_four",
]


class VerificationError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def json_file(path: Path) -> Any:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            require(key not in result, f"Duplicate JSON key {key!r}: {path}")
            result[key] = value
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)


def relative(value: Any) -> PurePosixPath:
    require(isinstance(value, str) and bool(value), "Empty or non-string source path")
    require("\\" not in value and "\0" not in value, f"Invalid source path: {value!r}")
    path = PurePosixPath(value)
    require(not path.is_absolute() and path.as_posix() == value,
            f"Non-canonical source path: {value!r}")
    require(all(p not in {"", ".", "..", ".git"} for p in path.parts),
            f"Source path traversal or Git metadata: {value!r}")
    return path


def contained(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def physical_path(root: Path, rel: str) -> Path:
    path = root.joinpath(*relative(rel).parts)
    for parent in path.parents:
        if parent == root:
            break
        require(not parent.is_symlink(), f"Source parent is a symlink: {parent}")
    return path


def inventory(root: Path) -> set[str]:
    require(root.is_dir() and not root.is_symlink(), f"Missing or linked source root: {root}")
    result: set[str] = set()
    for base, directories, files in os.walk(root, followlinks=False):
        for name in list(directories):
            item = Path(base) / name
            if item.is_symlink():
                result.add(item.relative_to(root).as_posix())
                directories.remove(name)
        for name in files:
            result.add((Path(base) / name).relative_to(root).as_posix())
    return result


def git_object(kind: str, raw: bytes) -> str:
    return hashlib.sha1(kind.encode("ascii") + b" " + str(len(raw)).encode("ascii") +
                        b"\0" + raw).hexdigest()


def file_bytes(root: Path, rel: str, mode: str) -> bytes:
    path = physical_path(root, rel)
    require(mode in {"100644", "100755", "120000"}, f"Unsupported mode {mode}: {rel}")
    info = path.lstat()
    if mode == "120000":
        require(stat.S_ISLNK(info.st_mode), f"Expected a symbolic link: {path}")
        target = os.readlink(path)
        require(not os.path.isabs(target), f"Absolute source symlink: {path}")
        require(contained(path.resolve(strict=True), root.resolve()),
                f"Escaping source symlink: {path}")
        return os.fsencode(target)
    require(stat.S_ISREG(info.st_mode), f"Expected a regular source file: {path}")
    if os.name == "posix":
        require(bool(info.st_mode & 0o111) == (mode == "100755"),
                f"Executable mode mismatch: {path}")
    return path.read_bytes()


def verify_bytes(raw: bytes, entry: dict[str, Any], label: str,
                 blob_key: str = "git_blob") -> None:
    require(isinstance(entry.get("bytes"), int) and not isinstance(entry["bytes"], bool),
            f"Invalid byte count: {label}")
    require(SHA1.fullmatch(str(entry.get(blob_key, ""))) is not None,
            f"Invalid Git blob hash: {label}")
    require(SHA256.fullmatch(str(entry.get("sha256", ""))) is not None,
            f"Invalid SHA256: {label}")
    require(len(raw) == entry["bytes"], f"Source byte count mismatch: {label}")
    require(git_object("blob", raw) == entry[blob_key], f"Git blob mismatch: {label}")
    require(hashlib.sha256(raw).hexdigest() == entry["sha256"],
            f"Source SHA256 mismatch: {label}")


def git_tree(entries: list[dict[str, Any]]) -> str:
    """Reconstruct an upstream Git tree, including directory ordering and modes."""
    root: dict[str, Any] = {}
    for entry in entries:
        parts = relative(entry["source_path"]).parts
        node = root
        for part in parts[:-1]:
            child = node.setdefault(part, {})
            require(isinstance(child, dict), f"File/directory collision: {entry['source_path']}")
            node = child
        require(parts[-1] not in node, f"Duplicate upstream path: {entry['source_path']}")
        node[parts[-1]] = (entry["mode"], entry["git_blob"])

    def encode(node: dict[str, Any]) -> str:
        records: list[tuple[bytes, bytes]] = []
        for name, item in node.items():
            is_tree = isinstance(item, dict)
            mode, digest = ("40000", encode(item)) if is_tree else item
            raw_name = name.encode("utf-8")
            records.append((raw_name + (b"/" if is_tree else b""),
                            mode.encode("ascii") + b" " + raw_name + b"\0" +
                            bytes.fromhex(digest)))
        return git_object("tree", b"".join(record for _, record in sorted(records)))

    return encode(root)


def verify_commit(snapshot: dict[str, Any]) -> bool:
    """Bind a supplied original commit object to its revision and source tree."""
    if "commit_raw_base64" not in snapshot:
        return False
    raw = base64.b64decode(snapshot["commit_raw_base64"], validate=True)
    require(git_object("commit", raw) == snapshot["revision"],
            f"Original Git commit hash mismatch: {snapshot['name']}")
    require(raw.startswith(b"tree " + snapshot["tree"].encode("ascii") + b"\n"),
            f"Original Git commit/tree mismatch: {snapshot['name']}")
    return True


class HeaderTokens:
    """Lex only the Lean header; nested comments cannot introduce false imports."""

    def __init__(self, text: str):
        self.text = text.removeprefix("\ufeff")
        self.pos = 0
        self.line = 1
        self.pending: tuple[str, str, int] | None = None

    def _next(self) -> tuple[str, str, int]:
        text = self.text
        while self.pos < len(text):
            i = self.pos
            if text[i].isspace():
                self.line += text[i] == "\n"
                self.pos += 1
            elif text.startswith("--", i):
                j = text.find("\n", i + 2)
                self.pos = len(text) if j < 0 else j
            elif text.startswith("/-", i):
                depth = 1
                self.pos += 2
                while depth:
                    require(self.pos < len(text), "Unterminated Lean header comment")
                    if text.startswith("/-", self.pos):
                        depth += 1
                        self.pos += 2
                    elif text.startswith("-/", self.pos):
                        depth -= 1
                        self.pos += 2
                    else:
                        self.line += text[self.pos] == "\n"
                        self.pos += 1
            else:
                break
        if self.pos == len(text):
            return ("end", "", self.line)
        start, line = self.pos, self.line
        if text[start] == "«":
            end = text.find("»", start + 1)
            require(end >= 0, "Unterminated escaped Lean module identifier")
            value = text[start + 1:end]
            require(bool(value) and not any(c in value for c in "/\\\0\n\r"),
                    "Invalid escaped Lean module identifier")
            self.pos = end + 1
            return ("escaped_identifier", value, line)
        if text[start].isalpha() or text[start] == "_":
            self.pos += 1
            while self.pos < len(text):
                char = text[self.pos]
                if not (char.isalnum() or char in "_'" or
                        (ord(char) > 127 and char.isidentifier())):
                    break
                self.pos += 1
            return ("identifier", text[start:self.pos], line)
        self.pos += 1
        return ("dot" if text[start] == "." else "other", text[start], line)

    def peek(self) -> tuple[str, str, int]:
        if self.pending is None:
            self.pending = self._next()
        return self.pending

    def take(self) -> tuple[str, str, int]:
        result = self.peek()
        self.pending = None
        return result


def module_parts(parts: list[str] | tuple[str, ...]) -> str:
    def render(part: str) -> str:
        simple = (bool(part) and (part[0].isalpha() or part[0] == "_") and
                  all(c.isalnum() or c in "_'" or (ord(c) > 127 and c.isidentifier())
                      for c in part[1:]))
        keywords = IMPORT_MODIFIERS | {"import", "module", "prelude"}
        return part if simple and part not in keywords else f"«{part}»"
    return ".".join(render(part) for part in parts)


def lean_imports(text: str) -> list[str]:
    tokens = HeaderTokens(text)
    imports: list[str] = []
    prelude = False
    while True:
        kind, value, _ = tokens.peek()
        if kind != "identifier":
            break
        if value in {"module", "prelude"}:
            prelude = prelude or value == "prelude"
            tokens.take()
            continue
        while tokens.peek()[0] == "identifier" and tokens.peek()[1] in IMPORT_MODIFIERS:
            tokens.take()
        if tokens.peek()[1] != "import":
            break
        tokens.take()
        while tokens.peek()[0] == "identifier" and tokens.peek()[1] in IMPORT_MODIFIERS:
            tokens.take()
        while True:
            kind, value, line = tokens.take()
            require(kind in {"identifier", "escaped_identifier"},
                    "Lean import lacks a module identifier")
            parts = [value]
            while tokens.peek()[0] == "dot":
                tokens.take()
                kind, value, line = tokens.take()
                require(kind in {"identifier", "escaped_identifier"}, "Malformed dotted Lean import")
                parts.append(value)
            require(all(part not in {"", ".", ".."} for part in parts),
                    "Invalid Lean import path")
            imports.append(module_parts(parts))
            nxt = tokens.peek()
            if (nxt[0] not in {"identifier", "escaped_identifier"} or nxt[2] != line or
                    (nxt[0] == "identifier" and
                     nxt[1] in IMPORT_MODIFIERS | {"import", "module", "prelude"})):
                break
    if not prelude and "Init" not in imports:
        imports.insert(0, "Init")
    return list(dict.fromkeys(imports))


def module_name(path: str) -> str:
    rel = relative(path)
    require(rel.suffix == ".lean", f"Not a Lean source: {path}")
    return module_parts(rel.with_suffix("").parts)


def git_read(directory: Path, *args: str) -> str:
    result = subprocess.run(["git", "-c", "core.fsmonitor=false", "-C", str(directory), *args],
                            check=False, capture_output=True, text=True, timeout=60)
    require(result.returncode == 0,
            f"Dependency Git verification failed at {directory}: {result.stderr.strip()}")
    return result.stdout.strip()


def verify(package_root: Path, dependency_root: Path | None, source_only: bool) -> dict[str, Any]:
    root = package_root.resolve(strict=True)
    source_manifest = root / "native-sources.json"
    source_raw = source_manifest.read_bytes()
    manifest = json_file(source_manifest)
    require(manifest.get("schema_version") == 1, "Unsupported native source manifest schema")
    require(manifest.get("toolchain") == TOOLCHAIN and
            (root / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
            "Native source toolchain mismatch")
    lock = json_file(root / "lake-manifest.json")
    locked = {p["name"]: p for p in lock["packages"]}
    require(len(locked) == len(lock["packages"]) == 9, "Expected nine distinct locked dependencies")
    snapshots = manifest.get("packages", [])
    require(len(snapshots) == 9 and {p["name"] for p in snapshots} == set(locked),
            "Native snapshots do not match all nine locked dependencies")
    native_root = root / "NativeSources"
    require(native_root.is_dir() and not native_root.is_symlink() and
            {p.name for p in native_root.iterdir()} == set(locked) | {"methlib"},
            "Undeclared or missing NativeSources package roots")
    registry: dict[str, list[tuple[Path, str]]] = defaultdict(list)
    upstream_reports = []
    source_roots: list[Path] = []

    def register(module: str, path: Path, owner: str) -> None:
        require(module.split(".")[0] not in COMPILER_ROOTS,
                f"Source shadows pinned compiler module: {module}")
        registry[module].append((path, owner))

    def normalized_url(url: Any) -> str:
        require(isinstance(url, str), "Invalid source URL")
        return url.removesuffix(".git").rstrip("/")

    for snapshot in snapshots:
        name = snapshot["name"]
        require(re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None, "Invalid dependency name")
        pin = locked[name]
        require(pin.get("type") == "git" and pin.get("subDir") in {None, ""},
                f"Unsupported locked dependency source: {name}")
        require(snapshot.get("revision") == pin["rev"] and SHA1.fullmatch(pin["rev"]) is not None,
                f"Dependency revision mismatch: {name}")
        require(normalized_url(snapshot.get("url")) == normalized_url(pin["url"]),
                f"Dependency URL mismatch: {name}")
        require(snapshot.get("root") == f"NativeSources/{name}", f"Unexpected snapshot root: {name}")
        directory = physical_path(root, snapshot["root"])
        source_roots.append(directory)
        files = snapshot.get("files", [])
        require(bool(files), f"Empty source snapshot: {name}")
        expected: set[str] = set()
        lean_files: list[dict[str, Any]] = []
        for entry in files:
            original = relative(entry["source_path"])
            stored = relative(entry["path"])
            neutral = original.with_name(original.name + ".upstream") if original.name in {
                ".gitignore", ".gitattributes"} else original
            if entry["mode"] == "120000":
                require(original.suffix != ".lean", f"Native Lean symlink is unsupported: {name}/{original}")
                neutral = neutral.with_name(neutral.name + ".upstream-symlink")
            stored_mode = "100644" if entry["mode"] == "120000" else entry["mode"]
            require(entry.get("stored_mode", entry["mode"]) == stored_mode,
                    f"Stored source mode mismatch: {name}/{stored}")
            require(stored == neutral, f"Unexpected stored source mapping: {name}/{stored}")
            require(stored.as_posix() not in expected, f"Duplicate stored source path: {name}/{stored}")
            expected.add(stored.as_posix())
            raw = file_bytes(directory, stored.as_posix(), stored_mode)
            verify_bytes(raw, entry, f"{name}/{original}")
            if entry["mode"] == "120000":
                target = raw.decode("utf-8")
                require(not Path(target).is_absolute() and "\0" not in target and
                        contained((directory / original).parent.joinpath(target).resolve(),
                                  directory.resolve()),
                        f"Unsafe inert upstream symlink payload: {name}/{original}")
            if original.suffix == ".lean":
                lean_files.append(entry)
                if original.name != "lakefile.lean":
                    register(module_name(original.as_posix()), directory / stored, name)
        actual = inventory(directory)
        require(actual == expected,
                f"Snapshot inventory mismatch for {name}: missing={sorted(expected-actual)[:8]}, "
                f"extra={sorted(actual-expected)[:8]}")
        tree = git_tree(files)
        require(tree == snapshot.get("tree"), f"Upstream Git tree mismatch: {name}")
        commit_bound = verify_commit(snapshot)
        for key, actual_count in (("file_count", len(files)), ("lean_file_count", len(lean_files)),
                                  ("source_bytes", sum(f["bytes"] for f in files))):
            require(key not in snapshot or snapshot[key] == actual_count,
                    f"Snapshot count metadata mismatch: {name}/{key}")
        cache_checked = 0
        if not source_only:
            require(dependency_root is not None, "Full verification requires --dependency-root")
            cache = dependency_root / name
            require(git_read(cache, "rev-parse", "HEAD") == pin["rev"], f"Cached revision mismatch: {name}")
            require(git_read(cache, "rev-parse", "HEAD^{tree}") == tree, f"Cached Git tree mismatch: {name}")
            for entry in lean_files:
                actual_lean = file_bytes(cache, entry["source_path"], entry["mode"])
                verify_bytes(actual_lean, entry, f"cached {name}/{entry['source_path']}")
                if entry["mode"] == "120000":
                    require((cache / entry["source_path"]).read_bytes() ==
                            (directory / entry["path"]).read_bytes(),
                            f"Cached Lean symlink target bytes mismatch: {name}/{entry['source_path']}")
                cache_checked += 1
        upstream_reports.append({"name": name, "revision": pin["rev"], "tree": tree,
                                 "files": len(files), "lean_files": len(lean_files),
                                 "bytes": sum(f["bytes"] for f in files),
                                 "original_commit_object_verified": commit_bound,
                                 "cached_lean_files_verified": cache_checked})

    methlib = manifest.get("methlib", {})
    require(methlib.get("root") == "NativeSources/methlib" and
            methlib.get("manifest") == "NativeSources/methlib/SOURCE_MANIFEST.json" and
            methlib.get("revision") == METHLIB_REVISION, "Methlib source identity mismatch")
    methroot = physical_path(root, methlib["root"])
    source_roots.append(methroot)
    meth = json_file(physical_path(root, methlib["manifest"]))
    require("manifest_sha256" not in methlib or methlib["manifest_sha256"] ==
            hashlib.sha256((methroot / "SOURCE_MANIFEST.json").read_bytes()).hexdigest(),
            "Methlib manifest hash mismatch")
    require(meth.get("upstream_commit") == METHLIB_REVISION and
            meth.get("upstream_repository") == "randogelist/Methlib" and
            meth.get("source_modifications") == [], "Methlib source provenance mismatch")
    require(meth.get("target_lean_toolchain") == TOOLCHAIN and
            meth.get("target_mathlib_commit") == locked["mathlib"]["rev"],
            "Methlib target configuration mismatch")
    require(meth.get("source_module_count") == len(meth["files"]) == 39,
            "Expected the complete 39-module Methlib closure")
    expected = {"SOURCE_MANIFEST.json", "README.md", "LICENSE_STATUS.md"}
    seen_modules: set[str] = set()
    for entry in meth["files"] + meth["provenance_files"]:
        rel = relative(entry["path"]).as_posix()
        require(entry["package_relative_path"] == f"NativeSources/methlib/{rel}",
                f"Methlib package-relative path mismatch: {rel}")
        require(rel not in expected, f"Duplicate Methlib source path: {rel}")
        expected.add(rel)
        raw = file_bytes(methroot, rel, "100644")
        verify_bytes(raw, entry, f"methlib/{rel}", "upstream_git_blob_sha")
        if "module" in entry:
            require(entry["module"] == module_name(rel), f"Methlib module path mismatch: {rel}")
            seen_modules.add(entry["module"])
            imports = [m for m in lean_imports(raw.decode("utf-8")) if m != "Init"]
            require(imports == entry["imports"], f"Methlib import metadata mismatch: {rel}")
            register(entry["module"], methroot / rel, "methlib")
    require(inventory(methroot) == expected, "Methlib source inventory mismatch")
    order = json_file(root / "methlib-module-order.json")
    require(order == meth["topological_order"] and len(order) == len(set(order)) == 39 and
            set(order) == seen_modules, "Methlib module schedule mismatch")
    positions = {name: i for i, name in enumerate(order)}
    for entry in meth["files"]:
        for dependency in entry["imports"]:
            if dependency.startswith("SingularClosure."):
                require(dependency in positions and positions[dependency] < positions[entry["module"]],
                        f"Methlib module order is not topological: {entry['module']}")
    names = [s.strip() for s in (root / "methlib-audit-targets.txt").read_text().splitlines()
             if s.strip() and not s.lstrip().startswith("#")]
    require(names == ENDPOINT_NAMES and [e["name"] for e in meth["selected_endpoints"]] == names,
            "Selected Methlib endpoint inventory mismatch")
    audit = (root / "MethlibEndpoints/Audit.lean").read_text(encoding="utf-8")
    require(re.findall(r"^#check @(\S+)$", audit, re.M) == names and
            re.findall(r"^#print axioms (\S+)$", audit, re.M) == names,
            "Methlib endpoint audit commands mismatch")

    if (root / "NSEMaxwell/Audit.lean").is_file():
        project_roots = [(root, "NSEMaxwell"), (root, "MethlibEndpoints"),
                         (root / "LocalDependencies/Maxwell", "MaxwellEndpoint"),
                         (root / "LocalDependencies/Forward", "NSEMaxwellForward"),
                         (root / "LocalDependencies/Reverse", "NSEMaxwellReverse")]
        audit_roots = ["NSEMaxwell.Audit", "MethlibEndpoints.Audit"]
    else:
        require((root / "MaxwellEndpoint/Audit.lean").is_file(), "No active package audit root")
        project_roots = [(root, "MaxwellEndpoint"), (root, "MethlibEndpoints")]
        audit_roots = ["MaxwellEndpoint.Audit", "MethlibEndpoints.Audit"]
    for directory, prefix in project_roots:
        require(not directory.is_symlink() and contained(directory.resolve(), root),
                f"Linked or escaping project source root: {directory}")
        paths = [directory / f"{prefix}.lean"]
        paths += sorted((directory / prefix).rglob("*.lean"))
        for path in paths:
            rel = path.relative_to(directory).as_posix()
            raw = file_bytes(directory, rel, "100644")
            raw.decode("utf-8")
            register(module_name(rel), path, "project")

    reachable: set[str] = set()
    compiler_modules: set[str] = set()
    owners: Counter[str] = Counter()
    pending = list(reversed(audit_roots))
    while pending:
        module = pending.pop()
        if module.split(".")[0] in COMPILER_ROOTS:
            compiler_modules.add(module)
            continue
        if module in reachable:
            continue
        choices = registry.get(module, [])
        require(len(choices) > 0, f"Missing reachable Lean source module: {module}")
        require(len(choices) == 1, f"Ambiguous reachable Lean source module: {module}")
        path, owner = choices[0]
        reachable.add(module)
        owners[owner] += 1
        pending.extend(reversed(lean_imports(path.read_text(encoding="utf-8"))))
    require(set(order) <= reachable, "Selected Methlib source closure is not fully reachable")
    return {
        "schema_version": 1, "status": "SOURCE_ONLY_PASS" if source_only else "PASS",
        "package_root": str(root), "source_only": source_only,
        "manifest_sha256": hashlib.sha256(source_raw).hexdigest(), "toolchain": TOOLCHAIN,
        "dependency_root": None if source_only else str(dependency_root.resolve()),
        "upstream_packages": upstream_reports, "upstream_package_count": len(upstream_reports),
        "upstream_files": sum(p["files"] for p in upstream_reports),
        "upstream_lean_files": sum(p["lean_files"] for p in upstream_reports),
        "methlib_modules": len(order), "methlib_revision": METHLIB_REVISION,
        "methlib_manifest_sha256": hashlib.sha256((methroot / "SOURCE_MANIFEST.json").read_bytes()).hexdigest(),
        "selected_methlib_endpoints": len(names), "source_roots": [str(p) for p in source_roots],
        "reachable_module_count": len(reachable), "reachable_by_package": dict(sorted(owners.items())),
        "missing_reachable_modules": 0, "ambiguous_reachable_modules": 0,
        "compiler_provided_roots": sorted(COMPILER_ROOTS),
        "compiler_provided_modules": sorted(compiler_modules), "local_lean_execution": False,
        "axiom_audit": "SEPARATE_COMPILER_AUDIT_REQUIRED",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    try:
        require(args.source_only or args.dependency_root is not None,
                "Full verification requires --dependency-root")
        package = args.package_root.resolve(strict=True)
        require(not contained(args.report.resolve(), package / "NativeSources"),
                "Verification report must not modify a native source snapshot")
        result = verify(package, args.dependency_root, args.source_only)
        exit_code = 0
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError) as error:
        result = {"schema_version": 1, "status": "FAIL", "source_only": args.source_only,
                  "package_root": str(args.package_root.absolute()), "error": str(error),
                  "local_lean_execution": False}
        exit_code = 1
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("status", "package_root", "error",
                     "upstream_package_count", "upstream_lean_files", "methlib_modules",
                     "reachable_module_count") if k in result}, ensure_ascii=False))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
