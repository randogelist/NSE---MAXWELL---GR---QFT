"""Cached concurrent Lake build, fail-closed freshness verification, exact shared audit."""
from __future__ import annotations
import hashlib
import re

HEADER = re.compile(r"^\S+\s+\[\d+/\d+\](?: \(Optional\))? (\w+) ([A-Za-z_][A-Za-z0-9_'.]*)(?: \([^\n]*\))?$")
SUCCEEDED = {"Reused", "Replayed", "Unpacked", "Fetched", "Built"}

def completed_modules(output, selected):
    """Completion text only selects candidates; it never establishes freshness."""
    candidates, blocks, current = set(), {n: [] for n in selected}, None
    for line in output.splitlines():
        match = HEADER.fullmatch(line)
        if match:
            verb, name = match.groups()
            current = name if name in selected else None
            if current and verb in SUCCEEDED:
                candidates.add(current)
        if current:
            blocks[current].append(line)
    return candidates, blocks

def execute(root, report, modules, kinds, verifier, run):
    names = [m["module"] for m in modules]
    selected = set(names)
    code, output = run(["lake", "--no-ansi", "--verbose", "--log-level=warning", "build", *names], "build-batch.log")
    candidates, blocks = completed_modules(output, selected)
    if code == 0:
        candidates = selected.copy()
    for n, lines in blocks.items():
        if lines:
            (report / ("build-" + n.replace(".", "-") + ".log")).write_text("\n".join(lines) + "\n", encoding="utf-8")
    candidates = [n for n in names if n in candidates]
    verified = set()
    if candidates:
        fresh_code, _ = run(["lake", "--no-ansi", "build", "--no-build", *candidates], "freshness-batch.log")
        if fresh_code == 0:
            verified.update(candidates)
        else:
            # A conservative fallback if output formatting ever misidentifies a
            # success. Every admitted module still needs a successful Lake
            # transitive-freshness check under the exact committed source bytes.
            for n in candidates:
                check, _ = run(["lake", "build", "--no-build", n], "freshness-" + n.replace(".", "-") + ".log")
                if check == 0:
                    verified.add(n)
    results, declarations, errors = [], [], []
    by_name = {}
    for item in modules:
        n = item["module"]
        result = {"module": n, "path": item["path"], "audit_targets": item["audit_targets"],
                  "build_status": "PASS" if n in verified else "FAIL_OR_BLOCKED",
                  "audit_status": "NOT_RUN" if n in verified else "SKIPPED_BUILD_FAILURE",
                  "cache_strategy": "BATCH_LAKE_BUILD_AND_SUCCESSFUL_TRANSITIVE_FRESHNESS_CHECK",
                  "batch_build_exit_code": code, "build_log": "build-batch.log"}
        if n in verified:
            artifact = root / ".lake/build/lib/lean" / (n.replace(".", "/") + ".olean")
            if not artifact.is_file():
                raise RuntimeError("Fresh module artifact missing: " + n)
            result["olean_sha256"] = hashlib.sha256(artifact.read_bytes()).hexdigest()
            result["freshness_exit_code"] = 0
        else:
            errors.append(n + ": no successful current-source freshness certificate")
            declarations.extend({"name": d, "module": n, "kind": kinds[d], "status": "SKIPPED_BUILD_FAILURE"}
                                for d in item["audit_targets"])
        results.append(result)
        by_name[n] = result
    if not verified:
        return results, declarations, errors
    audited = [m for m in modules if m["module"] in verified]
    source = "".join("import " + m["module"] + "\n" for m in audited)
    source += "set_option pp.universes true\nset_option pp.fullNames true\n"
    for m in audited:
        n = m["module"]
        source += '#eval IO.println "NSE_MODULE_BEGIN:' + n + '"\n'
        source += "".join("#check @" + d + "\n#print axioms " + d + "\n" for d in m["audit_targets"])
        source += '#eval IO.println "NSE_MODULE_END:' + n + '"\n'
    audit_path = report / "Batch-Audit.lean"
    audit_path.write_text(source, encoding="utf-8")
    source_hash = hashlib.sha256(audit_path.read_bytes()).hexdigest()
    audit_code, audit_output = run(["lake", "env", "lean", str(audit_path)], "audit-batch.log")
    global_failure = bool(audit_code or "sorryAx" in audit_output or re.search(r"(?:^|\n).*:\s*error:", audit_output))
    try:
        all_records = verifier.parse_axioms(audit_output)
        expected = {d for m in audited for d in m["audit_targets"]}
        if set(all_records) != expected:
            global_failure = True
    except Exception:
        global_failure = True
    for m in audited:
        n, targets = m["module"], m["audit_targets"]
        result = by_name[n]
        result.update(audit_source="Batch-Audit.lean", audit_source_sha256=source_hash,
                      audit_exit_code=audit_code, audit_log="audit-" + n.replace(".", "-") + ".log")
        begin, end = "NSE_MODULE_BEGIN:" + n + "\n", "NSE_MODULE_END:" + n + "\n"
        module_errors = []
        if audit_output.count(begin) != 1 or audit_output.count(end) != 1:
            segment = ""
            module_errors.append("Missing or duplicate module audit boundaries")
        else:
            segment = audit_output.split(begin, 1)[1].split(end, 1)[0]
        (report / result["audit_log"]).write_text(segment, encoding="utf-8")
        if global_failure:
            module_errors.append("Aggregate audit did not pass completely; no promotion")
        try:
            records = verifier.parse_axioms(segment)
            if set(records) != set(targets):
                module_errors.append("Exact module axiom records differ from targets")
            for d in targets:
                rows = records.get(d, [])
                if len(rows) != 1:
                    module_errors.append(d + ": missing or duplicate record")
                    declarations.append({"name": d, "module": n, "kind": kinds[d], "status": "MISSING_OR_DUPLICATE"})
                    continue
                axioms = sorted({verifier.normalize_axiom_name(a) for a in rows[0]})
                bad = sorted(set(axioms) - verifier.ALLOWED_AXIOMS)
                if bad:
                    module_errors.append(d + ": unapproved axioms " + str(bad))
                declarations.append({"name": d, "module": n, "kind": kinds[d],
                    "status": "PASS_STANDARD_ONLY" if not bad and not global_failure else "FAIL",
                    "axioms": axioms, "unapproved_axioms": bad})
        except Exception as error:
            module_errors.append("Module axiom parser failed: " + str(error))
        artifact = root / ".lake/build/lib/lean" / (n.replace(".", "/") + ".olean")
        if hashlib.sha256(artifact.read_bytes()).hexdigest() != result["olean_sha256"]:
            module_errors.append("Compiled artifact changed during audit")
        if module_errors:
            for row in declarations:
                if row["module"] == n and row["status"] == "PASS_STANDARD_ONLY":
                    row["status"] = "FAIL"
        result["audit_status"] = "FAIL" if module_errors else "PASS_STANDARD_ONLY"
        result["errors"] = module_errors
        errors.extend(n + ": " + e for e in module_errors)
    return results, declarations, errors
