#!/usr/bin/env python3
"""Pure runner-policy tests. No Lean, Lake, elan, or external process is executed."""
from __future__ import annotations

import unittest

from run_assembly import (audit_records, audit_source, batch_build_targets,
                          failed_assembly_modules, successful_dag_modules,
                          validate_batch_builds)


class BatchedAuditTests(unittest.TestCase):
    def setUp(self):
        self.stages = [
            ("assembly-001", "GRAssembly.Base", ["Test.base"]),
            ("assembly-002", "GRAssembly.Broken", ["Test.broken"]),
            ("assembly-003", "GRAssembly.Child", ["Test.child"]),
            ("assembly-004", "GRAssembly.Independent", ["Test.independent"]),
        ]
        self.closures = {
            "GRAssembly.Base": set(),
            "GRAssembly.Broken": {"GRAssembly.Base"},
            "GRAssembly.Child": {"GRAssembly.Base", "GRAssembly.Broken"},
            "GRAssembly.Independent": {"GRAssembly.Base"},
        }

    def test_unknown_batch_excludes_failures_and_transitive_dependents(self):
        actual = batch_build_targets(self.stages, {"GRAssembly.Base"},
                                     {"GRAssembly.Broken"}, self.closures)
        self.assertEqual(actual, ["GRAssembly.Independent"])

    def test_current_failure_overrides_reported_success(self):
        calls = []
        ready, failed, stats = validate_batch_builds(
            self.stages, {module for _, module, _ in self.stages},
            {"GRAssembly.Broken"}, self.closures,
            lambda command, log: calls.append((command, log)), True)
        self.assertEqual([module for _, module, _ in ready],
                         ["GRAssembly.Base", "GRAssembly.Independent"])
        self.assertEqual([entry["status"] for entry in failed],
                         ["FAIL", "BLOCKED_BY_FAILED_DEPENDENCY"])
        self.assertEqual(calls, [])
        self.assertEqual(stats["status"], "NOT_NEEDED")

    def test_successful_validation_batch_certifies_all_requested_targets(self):
        calls = []
        ready, failed, stats = validate_batch_builds(
            self.stages, {"GRAssembly.Base"}, {"GRAssembly.Broken"}, self.closures,
            lambda command, log: calls.append((command, log)), True)
        self.assertEqual(calls, [(["lake", "build", "GRAssembly.Independent"],
                                  "batch-validation-build.log")])
        self.assertEqual(len(ready), 2)
        self.assertEqual(len(failed), 2)
        self.assertEqual(stats["fallback_builds"], 0)

    def test_failed_validation_batch_requires_individual_success(self):
        calls = []

        def runner(command, log):
            calls.append((command, log))
            if log == "batch-validation-build.log" or command[-1] == "GRAssembly.Broken":
                raise ValueError("simulated nonzero exit")

        ready, failed, stats = validate_batch_builds(
            self.stages, {"GRAssembly.Base"}, set(), self.closures, runner, True)
        self.assertEqual([module for _, module, _ in ready],
                         ["GRAssembly.Base", "GRAssembly.Independent"])
        self.assertEqual([entry["status"] for entry in failed],
                         ["FAIL", "BLOCKED_BY_FAILED_DEPENDENCY"])
        self.assertEqual(stats["fallback_builds"], 2)
        self.assertFalse(any(command == ["lake", "build", "GRAssembly.Child"] for command, _ in calls))

    def test_full_dag_success_needs_no_redundant_build(self):
        def forbidden_runner(*_):
            self.fail("No second build is required after a complete current DAG success")

        ready, failed, stats = validate_batch_builds(
            self.stages, {module for _, module, _ in self.stages}, set(),
            self.closures, forbidden_runner, True)
        self.assertEqual(ready, self.stages)
        self.assertEqual(failed, [])
        self.assertEqual(stats["fallback_builds"], 0)

    def test_baseline_failure_remains_fatal(self):
        stages = [("adapter", "GRAdapter", ["Test.baseline"])]

        def runner(*_):
            raise ValueError("baseline build failure")

        with self.assertRaisesRegex(ValueError, "baseline build failure"):
            validate_batch_builds(stages, set(), set(), {"GRAdapter": set()}, runner, True)

    def test_audit_source_is_deterministic_with_paired_exact_targets(self):
        stages = [self.stages[0], ("assembly-005", "GRAssembly.Base", ["Test.other"]), self.stages[3]]
        text, targets = audit_source(stages)
        self.assertEqual(text.count("import GRAssembly.Base\n"), 1)
        self.assertNotIn("GRAssembly.Broken", text)
        self.assertEqual(targets, ["Test.base", "Test.other", "Test.independent"])
        self.assertEqual(text.count("#check @"), 3)
        self.assertEqual(text.count("#print axioms "), 3)
        self.assertEqual(audit_source(stages), (text, targets))

    def test_duplicate_target_is_rejected_before_audit(self):
        with self.assertRaisesRegex(ValueError, "Duplicate target"):
            audit_source([self.stages[0], ("assembly-005", "GRAssembly.Other", ["Test.base"])])

    def test_invalid_module_or_name_cannot_inject_lean_commands(self):
        for stages in [[("x", "Bad\nimport Evil", ["Test.base"])],
                       [("x", "Good", ["Test.base\naxiom bad : False"])]]:
            with self.assertRaises(ValueError):
                audit_source(stages)

    def test_complete_audit_preserves_named_axiom_records(self):
        log = ("'Test.base' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
               "'Test.other' does not depend on any axioms\n")
        records = audit_records(log, ["Test.base", "Test.other"])
        self.assertEqual([r["name"] for r in records], ["Test.base", "Test.other"])
        self.assertEqual(records[1]["axioms"], [])

    def test_missing_duplicate_and_unapproved_axioms_are_rejected(self):
        good = "'Test.base' depends on axioms: [propext]\n"
        for log, targets in [(good, ["Test.base", "Test.other"]),
                             (good + good, ["Test.base"]),
                             ("'Test.base' depends on axioms: [unapproved]\n", ["Test.base"]),
                             ("'Test.base' depends on axioms: [sorryAx]\n", ["Test.base"])]:
            with self.assertRaises(ValueError):
                audit_records(log, targets)

    def test_current_dag_failure_is_not_a_success(self):
        log = ("✔ [1/4] Replayed GRAssembly.Base\n"
               "✔ [2/4] Built GRAssembly.Broken (1.2s)\n"
               "error: GRAssembly/Broken.lean:5:1: bad proof\n"
               "⚠ [4/4] Replayed GRAssembly.Independent\n")
        modules = {m for _, m, _ in self.stages}
        self.assertEqual(failed_assembly_modules(log, modules), {"GRAssembly.Broken"})
        self.assertEqual(successful_dag_modules(log, modules),
                         {"GRAssembly.Base", "GRAssembly.Independent"})


if __name__ == "__main__":
    unittest.main()
