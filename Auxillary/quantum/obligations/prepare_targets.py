#!/usr/bin/env python3
"""Prepare committed obligation audit targets by static source inspection; never runs Lean."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
ORDER = {x: i for i, x in enumerate((
    "Flow", "Fourier", "Galerkin", "Gaussian", "Transport", "CompleteFlow",
    "GlobalDrift", "CanonicalFlow", "FlowContinuity", "FlowDependence",
    "Admissibility", "PacketEstimates",
))}

def without_comments(text):
    # Preserve line boundaries; nested Lean block comments are allowed.
    out, depth, i, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif not quoted and text.startswith("/-", i):
            depth = 1
            i += 2
        elif not quoted and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        else:
            ch = text[i]
            out.append(ch)
            if ch == '"' and (i == 0 or text[i - 1] != "\\"):
                quoted = not quoted
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment.")
    return "".join(out)

def declarations(path):
    stack, found = [], []
    for number, raw in enumerate(without_comments(path.read_text()).splitlines(), 1):
        if raw and raw[0].isspace():
            continue  # Candidate extraction is deliberately restricted to top-level commands.
        line = raw.strip()
        while line.startswith("@[") and "]" in line:
            line = line.split("]", 1)[1].lstrip()
        m = re.fullmatch(r"namespace\s+([^\s]+)", line)
        if m:
            if not NAME.fullmatch(m[1]):
                raise ValueError(f"Unsupported namespace at {path}:{number}")
            stack.append(("namespace", m[1]))
            continue
        if re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+[^\s]+)?", line):
            stack.append(("section", ""))
            continue
        if re.fullmatch(r"end(?:\s+[^\s]+)?", line):
            if not stack:
                raise ValueError(f"Unmatched end at {path}:{number}")
            stack.pop()
            continue
        m = re.match(r"((?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(theorem|lemma|def|abbrev)\s+([^\s:(\[{]+)", line)
        if m and "private" not in m[1].split():
            kind, name = m[2], m[3]
            prefix = ".".join(n for k, n in stack if k == "namespace")
            name = name.removeprefix("_root_.") if name.startswith("_root_.") else (prefix + "." if prefix else "") + name
            if not NAME.fullmatch(name):
                raise ValueError(f"Unsupported declaration name at {path}:{number}: {name}")
            found.append({"name": name, "kind": kind})
    if stack:
        raise ValueError(f"Unclosed namespace/section in {path}")
    return found

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[3])
    p.add_argument("--module", action="append", default=[])
    args = p.parse_args()
    root = args.repo_root.resolve()
    if args.module:
        files = [root / "Quantum_adapter" / (n.replace(".", "/") + ".lean") for n in args.module]
    else:
        files = sorted((root / "Quantum_adapter/QuantumAdapter/Obligations").rglob("*.lean"))
        final = root / "Quantum_adapter/QuantumAdapter/Obligations.lean"
        if final.is_file():
            files.append(final)
    by_name, dependencies, empty = {}, {}, []
    for path in files:
        module = path.relative_to(root / "Quantum_adapter").with_suffix("").as_posix().replace("/", ".")
        if not (module == "QuantumAdapter.Obligations" or module.startswith("QuantumAdapter.Obligations.")):
            raise ValueError("Unexpected module: " + module)
        body = without_comments(path.read_text())
        if re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", body):
            raise ValueError("Admission or unsafe source rejected: " + module)
        selected = declarations(path)
        if not selected:
            empty.append(path.relative_to(root).as_posix())
            continue
        if module in by_name:
            raise ValueError("Duplicate module: " + module)
        by_name[module] = {"module": module, "path": path.relative_to(root).as_posix(), "audit_targets": [d["name"] for d in selected], "declaration_kinds": {d["name"]: d["kind"] for d in selected}}
        imported = set()
        for line in body.splitlines():
            if line.startswith("import "):
                imported.update(line.split()[1:])
        dependencies[module] = {n for n in imported if n == "QuantumAdapter.Obligations" or n.startswith("QuantumAdapter.Obligations.")}
    for module, deps in dependencies.items():
        missing = deps - set(by_name)
        if missing:
            raise ValueError(f"Unselected obligation dependencies of {module}: {sorted(missing)}")
    modules, pending = [], dict(by_name)
    while pending:
        ready = sorted(n for n in pending if not (dependencies[n] & set(pending)))
        if not ready:
            raise ValueError("Obligation import cycle")
        for n in ready:
            modules.append(pending.pop(n))
    names = [d for module in modules for d in module["audit_targets"]]
    if not names or len(names) != len(set(names)):
        raise ValueError("No targets or duplicate fully qualified declarations")
    out = root / "Auxillary/quantum/obligations"
    out.mkdir(parents=True, exist_ok=True)
    (out / "module-targets.json").write_text(json.dumps(modules, indent=2) + "\n")
    (out / "audit-targets.txt").write_text("\n".join(names) + "\n")
    print(json.dumps({"status": "STATIC_CANDIDATE_REQUIRES_REVIEW", "modules": len(modules), "declarations": len(names), "theorems": sum(k in {"theorem", "lemma"} for m in modules for k in m["declaration_kinds"].values()), "empty_modules_excluded": empty, "lean_executions": 0}))

if __name__ == "__main__":
    main()
