# Formalization contract

TARGET = forall nu > 0, forall c > 0, FeffermanB nu iff MaxwellB nu c.

1. Preserve the concrete unforced periodic three-dimensional problem, arbitrary velocity mean, periodic pressure, and joint C-infinity regularity through t = 0.
2. Do not replace the concrete theorem by arbitrary proposition variables or an adjusted mean-zero theorem.
3. Do not execute Lean, Lake, or elan in the local authoring environment. Compilation occurs externally using Lean 4.34.0-rc1. The active CI target is native Linux (Ubuntu 24.04), as requested on 2026-11-13. The literal requested directory names contain `<` and `>` and require a POSIX checkout; Auxillary/run.cmd and Windows certificates are retained as historical entry points/evidence, not a current native-Windows-checkout guarantee.
4. Preserve dependency and compilation caches. Do not invoke clean, cache clean, or cache get!.
5. No sorry, admit, unproved opaque body, new axiom, unsafe proof construction, or native_decide proof axiom.
6. Approved foundational axioms: propext, Classical.choice, Quot.sound.
7. Prepared code has status A_TIER_CANDIDATE. Matching external compilation and theorem-level axiom-audit evidence are necessary for A_TIER.
8. Theorem hypotheses are not discharged by an axiom audit. Every analytic, semantic, certificate, witness, or admission premise must remain explicit.
9. CONDITIONAL_FORMAL_CLOSURE applies only to the exact audited implication, with every unresolved premise named. UNCONDITIONAL_CLOSURE requires discharge of all such premises.
10. The concrete target is `NSEMaxwell.Classical.ExactEquivalence`. A definition of this proposition is not a proof of it.
11. Preserve the requested domain layout: Fefferman_B_adapter contains exact statements, shared calculus, and copied endpoints; B <-> Maxwell/=> and B <-> Maxwell/<= contain the two directions. Copied .lean.txt sources remain references until explicitly integrated and audited.
12. Store runners, audit/cache target lists, status records, infrastructure documentation, and retained compiler evidence under the literal top-level Auxillary directory. Keep GitHub workflow discovery, Lake/toolchain configuration, repository metadata, README.md, and this instruction file at their required root locations. Preserve historical certificate bytes and embedded source paths when relocating evidence. External Linux entry point: bash Auxillary/run.sh.
