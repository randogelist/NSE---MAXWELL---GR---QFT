#!/usr/bin/env python3
"""Synthetic evidence and tampering checks; no compiler or subprocess is invoked."""
from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from run_assembly import ALLOWED, COMPILER_COMMIT, MATHLIB, TOOLCHAIN, audit_source, digest
from verify_assembly import current_source_paths, stage_layout, verify


class EvidenceFixture:
    def __init__(self, root, *, partial=False, batch=True, individual=True):
        self.repo, self.evidence = root / "repo", root / "evidence"
        self.repo.mkdir(); self.evidence.mkdir()
        self.commit = "a" * 40
        self.baseline = {"adapter": [f"Test.base{i}" for i in range(399)],
                         "forward": ["Test.forward"], "reverse": ["Test.reverse"]}
        self.cutouts = [{"module": "TempEndpoint", "name": f"Test.cutout{i}"} for i in range(85)]
        self.inventory = [{"module": "GRAssembly.Base", "name": f"Test.certified{i}"} for i in range(171)]
        self.inventory += [{"module": "GRAssembly.Broken", "name": "Test.broken"},
                           {"module": "GRAssembly.Child", "name": "Test.child"}]
        self.lock = {"packages": [{"type": "git", "name": "mathlib", "rev": MATHLIB}]}
        for name in ("ASSEMBLY", "GR_adapter", "TEMP"):
            self.put(self.repo, name + "/lean-toolchain", TOOLCHAIN + "\n")
            self.json(self.repo, name + "/lake-manifest.json", self.lock)
        for name in ("run.cmd", "run.sh"):
            self.put(self.repo, "ASSEMBLY/" + name, "fixture runner\n")
        self.put(self.repo, "Auxillary/GR/Assembly/scripts/run_assembly.py", "# fixture source\n")
        for module, imports in {"Base": [], "Broken": ["Base"], "Child": ["Broken"],
                                "CertifiedBase": ["Base"]}.items():
            self.put(self.repo, f"ASSEMBLY/GRAssembly/{module}.lean",
                     "".join(f"import GRAssembly.{x}\n" for x in imports))
        self.put(self.repo, "ASSEMBLY/GRAssembly.lean", "import GRAssembly.Child\n")
        self.put(self.repo, "TEMP/TempEndpoints.lean", "import TempEndpoint\n")
        self.json(self.repo, "Auxillary/GR/audit-targets.json", self.baseline)
        self.json(self.repo, "Auxillary/TEMP/audit-targets.json", self.cutouts)
        self.json(self.repo, "Auxillary/GR/Assembly/audit-targets.json", self.inventory)
        self.json(self.repo, "Auxillary/GR/Assembly/certified-base-targets.json",
                  [x["name"] for x in self.inventory[:171]])
        self.json(self.repo, "Auxillary/GR/Assembly/formalization-status.json", {"fixture": True})
        scope = {"fixture": True, "selected_modules": sorted({x["module"] for x in self.inventory}),
                 "selected_new_target_count": 173, "full_new_target_count": 173,
                 "baseline_target_count": 401, "cutout_target_count": 85,
                 "cutout_validation": "FRESH_NAMED_AXIOM_AUDITS; SOURCE_TYPE_EQUALITY_RETAINS_PRIOR_CERTIFICATE",
                 "selection_mode": "full"}
        self.json(self.evidence, "declared-scope.json", scope)
        stages, _ = stage_layout(self.repo, self.baseline, [x["name"] for x in self.cutouts], self.inventory, individual)
        failed_modules = {"GRAssembly.Broken", "GRAssembly.Child"} if partial else set()
        ready = [s for s in stages if s[1] not in failed_modules]
        failed = []
        for stage, module, _ in stages:
            if module in failed_modules:
                entry = {"stage": stage, "module": module,
                         "status": "FAIL" if module.endswith("Broken") else "BLOCKED_BY_FAILED_DEPENDENCY"}
                if module.endswith("Child"):
                    entry["dependencies"] = ["GRAssembly.Broken"]
                else:
                    entry["error"] = "Explicit compiler error in shared DAG build; log=dag-build.log"
                failed.append(entry)
                self.json(self.evidence, stage + "-summary.json", entry)
        dag_text = "".join(f"✔ [1/1] Built {module}\n" for _, module, _ in ready)
        if partial:
            dag_text += "error: GRAssembly/Broken.lean:1:1: fixture failure\n"
        self.put(self.evidence, "dag-build.log", dag_text)
        commands = [{"command": ["lake", "build", *[s[1] for s in stages]],
                     "log": "dag-build.log", "exit_code": int(partial)}]
        entries = []
        if batch:
            self.make_audit(commands, "BatchAudit.lean", "batch-audit.log", ready)
        for stage, module, names in ready:
            audit_name = "BatchAudit.lean" if batch else stage.replace("-", "_").title() + "Audit.lean"
            log_name = "batch-audit.log" if batch else stage + "-audit.log"
            if not batch:
                self.make_audit(commands, audit_name, log_name, [(stage, module, names)])
            entry = {"stage": stage, "module": module, "status": "PASS_STANDARD_ONLY",
                     "source_commit": self.commit, "target_count": len(names),
                     "audit_mode": "FRESH_BATCH" if batch else "FRESH_STAGE",
                     "audit_source": audit_name, "audit_log": log_name,
                     "audit_source_sha256": digest(self.evidence / audit_name),
                     "audit_log_sha256": digest(self.evidence / log_name),
                     "targets": [{"name": name, "status": "PASS_STANDARD_ONLY", "axioms": []} for name in names]}
            entries.append(entry)
            self.json(self.evidence, stage + "-summary.json", entry)
        version = f"Lean (version 4.34.0-rc1, x86_64-unknown-linux-gnu, commit {COMPILER_COMMIT}, Release)"
        self.put(self.evidence, "lean-version-build.log", version + "\n")
        self.put(self.evidence, "dependency-mathlib-revision.log", MATHLIB + "\n")
        self.put(self.evidence, "dependency-mathlib-working-tree.log", "")
        manifest = {"source_commit": self.commit, "source_roots": ["ASSEMBLY", "GR_adapter", "TEMP"],
                    "files": [{"path": name, "sha256": digest(self.repo / name)} for name in sorted(current_source_paths(self.repo))]}
        self.json(self.evidence, "source-manifest.json", manifest)
        status = "PARTIAL_STANDARD_ONLY" if partial else "PASS_STANDARD_ONLY"
        self.summary = {"schema_version": 1, "status": status, "source_commit": self.commit,
                        "source_input_verification": "PASS", "actual_mathlib_commit": MATHLIB,
                        "actual_lean_version": version, "allowed_axioms": sorted(ALLOWED),
                        "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
                        "source_manifest_sha256": digest(self.evidence / "source-manifest.json"),
                        "baseline_target_count": 401, "cutout_target_count": 85, "new_target_count": 173,
                        "target_count": sum(len(s[2]) for s in ready), "declared_scope": scope,
                        "stages": entries, "failed_stages": failed}
        self.provenance = {"schema_version": 1, "phase": "build", "status": status,
                           "source_commit": self.commit, "requested_toolchain": TOOLCHAIN,
                           "requested_compiler_commit": COMPILER_COMMIT, "requested_mathlib_commit": MATHLIB,
                           "actual_mathlib_commit": MATHLIB, "actual_lean_version": version,
                           "source_manifest_sha256": self.summary["source_manifest_sha256"],
                           "cache_policy": "PRESERVE_AND_REUSE_COMPATIBLE_OBJECTS",
                           "semantic_discharge": "NOT_INFERRED_FROM_AXIOM_AUDIT",
                           "root_promotion": "REQUIRES_EXACT_ROOT_TYPE_AND_PREMISE_REVIEW",
                           "external_platform": "linux", "dependency_revisions": [{"name": "mathlib", "revision": MATHLIB}],
                           "stages": entries, "failed_stages": failed, "commands": commands}
        self.flush()

    def put(self, root, name, text):
        path = root / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)

    def json(self, root, name, value):
        self.put(root, name, json.dumps(value, indent=2) + "\n")

    def make_audit(self, commands, name, log_name, stages):
        text, names = audit_source(stages)
        self.put(self.evidence, name, text)
        self.put(self.evidence, log_name, "".join(f"'{n}' does not depend on any axioms\n" for n in names))
        commands.append({"command": ["lake", "env", "lean", "-R", "/fixture/evidence", "/fixture/evidence/" + name],
                         "log": log_name, "exit_code": 0})

    def flush(self):
        self.json(self.evidence, "audit-summary.json", self.summary)
        self.json(self.evidence, "provenance-build.json", self.provenance)
        for entry in self.summary["stages"] + self.summary["failed_stages"]:
            self.json(self.evidence, entry["stage"] + "-summary.json", entry)

    def check(self, allow_partial=False):
        self.flush()
        return verify(self.repo, self.evidence, self.commit, allow_partial)


class EvidenceVerificationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def fixture(self, **kwargs):
        return EvidenceFixture(self.root, **kwargs)

    def test_batch_full_exact_inventory(self):
        result = self.fixture().check()
        self.assertEqual(result["status"], "PASS_STANDARD_ONLY")
        self.assertEqual(result["target_count"], 659)
        self.assertEqual(result["unresolved_target_count"], 0)
        self.assertEqual(result["root_promotion"], "NOT_INFERRED_FROM_EVIDENCE_VERIFICATION")

    def test_partial_requires_opt_in_and_retains_unresolved_targets(self):
        f = self.fixture(partial=True)
        with self.assertRaisesRegex(ValueError, "allow-partial"):
            f.check()
        result = f.check(True)
        self.assertEqual(result["status"], "PARTIAL_STANDARD_ONLY")
        self.assertEqual(result["unresolved_target_count"], 2)
        self.assertEqual(result["failed_stage_count"], 2)

    def test_individual_stage_audits_and_noncontiguous_numbers(self):
        f = self.fixture(batch=False)
        ids = [s["stage"] for s in f.summary["stages"]]
        self.assertIn("assembly-certified-base", ids)
        self.assertNotIn("assembly-001", ids)
        self.assertIn("assembly-002", ids)
        self.assertEqual(f.check()["target_count"], 659)

    def test_historical_aggregated_stage_audits(self):
        self.assertEqual(self.fixture(individual=False, batch=False).check()["target_count"], 659)

    def test_missing_stage_is_rejected(self):
        f = self.fixture(); f.summary["stages"].pop()
        with self.assertRaisesRegex(ValueError, "partition"):
            f.check()

    def test_forged_full_pass_with_failed_inventory_is_rejected(self):
        f = self.fixture(partial=True)
        f.summary["status"] = f.provenance["status"] = "PASS_STANDARD_ONLY"
        with self.assertRaisesRegex(ValueError, "status disagree"):
            f.check()

    def test_failed_batch_audit_cannot_supply_success_records(self):
        f = self.fixture(); f.provenance["commands"][-1]["exit_code"] = 1
        with self.assertRaisesRegex(ValueError, "fresh audit"):
            f.check()

    def test_failed_build_without_current_success_cannot_certify_batch(self):
        f = self.fixture(); f.provenance["commands"][0]["exit_code"] = 1
        f.put(f.evidence, "dag-build.log", "failed before compilation\n")
        with self.assertRaisesRegex(ValueError, "current successful build"):
            f.check()

    def test_build_after_audit_is_rejected(self):
        f = self.fixture(); f.provenance["commands"].reverse()
        with self.assertRaisesRegex(ValueError, "before audit"):
            f.check()

    def test_current_explicit_failure_overrides_apparent_success(self):
        f = self.fixture(); f.provenance["commands"][0]["exit_code"] = 1
        with (f.evidence / "dag-build.log").open("a") as out:
            out.write("error: GRAssembly/Broken.lean:1:1: current failure\n")
        with self.assertRaisesRegex(ValueError, "Failed module"):
            f.check()

    def test_tampered_source_even_with_updated_audit_hash_is_rejected(self):
        f = self.fixture(); path = f.evidence / "BatchAudit.lean"
        path.write_text(path.read_text().replace("#check @Test.base0\n", ""))
        for entry in f.summary["stages"]:
            entry["audit_source_sha256"] = digest(path)
        with self.assertRaisesRegex(ValueError, "exact current inventory"):
            f.check()

    def test_unapproved_axiom_even_with_updated_log_hash_is_rejected(self):
        f = self.fixture(); path = f.evidence / "batch-audit.log"
        path.write_text(path.read_text().replace("'Test.base0' does not depend on any axioms",
                                               "'Test.base0' depends on axioms: [unapproved]"))
        for entry in f.summary["stages"]:
            entry["audit_log_sha256"] = digest(path)
        with self.assertRaisesRegex(ValueError, "Unapproved"):
            f.check()

    def test_missing_raw_record_even_with_updated_hash_is_rejected(self):
        f = self.fixture(); path = f.evidence / "batch-audit.log"
        path.write_text("\n".join(path.read_text().splitlines()[1:]) + "\n")
        for entry in f.summary["stages"]:
            entry["audit_log_sha256"] = digest(path)
        with self.assertRaisesRegex(ValueError, "Expected one named"):
            f.check()

    def test_wrong_audit_directory_is_rejected(self):
        f = self.fixture(); f.provenance["commands"][-1]["command"][-2] = "/unrelated"
        with self.assertRaisesRegex(ValueError, "fresh audit"):
            f.check()

    def test_source_pin_manifest_and_summary_tampering_rejected(self):
        f = self.fixture()
        f.put(f.repo, "ASSEMBLY/lean-toolchain", "wrong toolchain\n")
        with self.assertRaisesRegex(ValueError, "Source bytes differ"):
            f.check()

    def test_failed_audit_batch_with_fresh_individual_fallback_is_accepted(self):
        f = self.fixture(batch=False)
        f.put(f.evidence, "batch-audit.log", "failed batch\n")
        f.provenance["commands"].insert(1, {"command": ["lake", "env", "lean", "-R", "/fixture/evidence",
                                                                 "/fixture/evidence/BatchAudit.lean"],
                                           "log": "batch-audit.log", "exit_code": 1})
        self.assertEqual(f.check()["status"], "PASS_STANDARD_ONLY")


if __name__ == "__main__":
    unittest.main()
