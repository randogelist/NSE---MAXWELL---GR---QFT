# Formalization contract

TARGET = forall nu > 0, forall c > 0, FeffermanB nu iff MaxwellB nu c.

1. Preserve the concrete unforced periodic three-dimensional problem, arbitrary velocity mean, periodic pressure, and joint C-infinity regularity through t = 0.
2. Do not replace the concrete theorem by arbitrary proposition variables or an adjusted mean-zero theorem.
3. Do not execute Lean, Lake, or elan in the local authoring environment. Compilation occurs externally using Lean 4.34.0-rc1. The active CI target is native Linux (Ubuntu 24.04), as requested on 2026-11-13; the native Windows run.cmd entry point remains supported.
4. Preserve dependency and compilation caches. Do not invoke clean, cache clean, or cache get!.
5. No sorry, admit, unproved opaque body, new axiom, unsafe proof construction, or native_decide proof axiom.
6. Approved foundational axioms: propext, Classical.choice, Quot.sound.
7. Prepared code has status A_TIER_CANDIDATE. Matching external compilation and theorem-level axiom-audit evidence are necessary for A_TIER.
8. Theorem hypotheses are not discharged by an axiom audit. Every analytic, semantic, certificate, witness, or admission premise must remain explicit.
9. CONDITIONAL_FORMAL_CLOSURE applies only to the exact audited implication, with every unresolved premise named. UNCONDITIONAL_CLOSURE requires discharge of all such premises.
10. The concrete target is `NSEMaxwell.Classical.ExactEquivalence`. A definition of this proposition is not a proof of it.
