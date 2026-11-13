#!/usr/bin/env python3
"""Prepare explicit candidate theorem targets by static source inspection; never runs Lean."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
ORDER = {x: i for i, x in enumerate(("Flow", "Fourier", "Galerkin", "Gaussian", "Transport", "PacketEstimates"))}

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
        m = re.match(r"((?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(?:theorem|lemma)\s+([^\s:(\[{]+)", line)
        if m and "private" not in m[1].split():
            name = m[2]
            prefix = ".".join(n for k, n in stack if k == "namespace")
            name = name.removeprefix("_root_.") if name.startswith("_root_.") else (prefix + "." if prefix else "") + name
            if not NAME.fullmatch(name):
                raise ValueError(f"Unsupported declaration name at {path}:{number}: {name}")
            found.append(name)
    if stack:
        raise ValueError(f"Unclosed namespace/section in {path}")
    return found

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[3])
    args = p.parse_args()
    root = args.repo_root.resolve()
    folder = root / "Quantum_adapter/QuantumAdapter/Assembly"
    files = sorted(folder.glob("*.lean"), key=lambda q: (ORDER.get(q.stem, 99), q.name))
    final = root / "Quantum_adapter/QuantumAdapter/Assembly.lean"
    if final.is_file():
        files.append(final)
    modules, names, empty = [], [], []
    for path in files:
        selected = declarations(path)
        if not selected:
            empty.append(path.relative_to(root).as_posix())
            continue
        module = path.relative_to(root / "Quantum_adapter").with_suffix("").as_posix().replace("/", ".")
        modules.append({"module": module, "path": path.relative_to(root).as_posix(), "audit_targets": selected})
        names.extend(selected)
    if not names or len(names) != len(set(names)):
        raise ValueError("No candidate targets or duplicate fully qualified declarations.")
    output = root / "Auxillary/quantum/assembly"
    (output / "module-targets.json").write_text(json.dumps(modules, indent=2) + "\n")
    (output / "audit-targets.txt").write_text("\n".join(names) + "\n")
    print(json.dumps({"status": "STATIC_CANDIDATE_REQUIRES_REVIEW", "modules": len(modules), "declarations": len(names),
                      "empty_modules_excluded": empty, "root_module_included": final.is_file(), "lean_executions": 0}))

if __name__ == "__main__":
    main()
