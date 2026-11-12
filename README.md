# NSE–Maxwell equivalence

Formalization target:

```text
∀ ν > 0, ∀ c > 0, FeffermanB ν ↔ MaxwellB ν c
```

The target is the classical, unforced, three-dimensional periodic Navier–Stokes problem with arbitrary velocity mean and periodic pressure, and its precisely constrained Maxwell formulation.

Development uses Lean 4.34.0-rc1. Compilation is external on native Windows, with cached dependencies. A theorem is not certified until matching compilation and theorem-level axiom-audit evidence exists. Analytic premises must be discharged separately from any conditional transfer theorem.
