# Classical mechanics adapter

```text
STATUS = A_TIER_CANDIDATE
ROOT = ClassicalMechanics.CLASSICAL_MECHANICS_ADAPTER
ROOT_TYPE = GlobalExactEquivalence ∧ FiniteExactEquivalence
LOCAL_LEAN_RUNS = 0
```

The first native endpoint is incompressible Newtonian **local Cauchy momentum balance** with the literal stress tensor and its actual derivative. It preserves arbitrary velocity means, the given velocity and pressure, and the initial datum.

| Module | Exact role |
|---|---|
| `ClassicalMechanics/Stress.lean` | `σ = -p I + 2νD(u)`; actual row divergence; full `grad div` term and its incompressible specialization |
| `ClassicalMechanics/Definitions.lean` | Global Newtonian predicate with the repository's arbitrary periodic pressure gauge |
| `ClassicalMechanics/FiniteSlab.lean` | Separate closed `[0,T]` predicates with actual `derivWithin (Icc 0 T)` and normalized pressure |
| `../B <-> ClassicalMechanics/=>/ClassicalMechanicsForward.lean` | NSE ⇒ Newtonian balance, first for supplied trajectories and then existence |
| `../B <-> ClassicalMechanics/<=/ClassicalMechanicsReverse.lean` | Newtonian balance ⇒ NSE, preserving the same fields |
| `ClassicalMechanics/Equivalence.lean` | Deterministic global and finite equivalence assembly |
| `ClassicalMechanics/MaxwellBridge.lean` | Both Maxwell implications, retaining `NSEMaxwell.Bridge.FourierHodgeLaws` |
| `ClassicalMechanics.lean` | Exact first adapter root |
| `ClassicalMechanics/Audit.lean` | Fresh named theorem-level axiom audit |

```lean
ClassicalMechanics.global_exact_equivalence
ClassicalMechanics.finite_exact_equivalence
ClassicalMechanics.CLASSICAL_MECHANICS_ADAPTER
```

The global root is `∀ ν > 0, FeffermanB ν ↔ NewtonianB ν`. The finite root is the equivalence of the two literal predicates on the same closed slab, with `scalarMean (p t) = 0`. These two pressure/time conventions remain separate.

The proof of stress divergence includes the unrestricted identity

```text
tensorDivergence (newtonianStress ν a p)
  = -gradient p + ν • laplacian a + ν • gradient (divergence a).
```

Incompressibility discharges the last term. No Fourier/Hodge law, flow-existence law, or constitutive divergence identity is supplied as an analytic assumption to the first adapter.

The complete B-tier reference and all 57 identity groups are indexed under `Auxillary/derivations/` and `Auxillary/classical-mechanics-proof-spine.json`. Actual material-flow existence, volume preservation, moving-region balance, and constrained Lagrange–d'Alembert equivalence remain separate pending formalization targets. The local Cauchy result does not establish those larger solution-set bijections or arbitrary-data global existence.

The active repository toolchain is external native Linux Lean `4.34.0-rc1`, Mathlib `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. The historical B-tier source catalog retains its original `4.33.0` pins; only concrete declarations used by the native sources are ported here.

External validation: the cached GitHub workflow first compiles and freshly audits this adapter, then retains all original integrated and isolated package checks. Evidence is recorded under `artifacts/external-linux/classical-mechanics/`; status promotion requires matching source hashes and theorem-level audit evidence.
