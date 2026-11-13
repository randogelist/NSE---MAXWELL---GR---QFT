# GR proof spine and exact remaining endpoints

```text
NATIVE_SOURCE != EXTERNAL_KERNEL_PASS
EXTERNAL_AXIOM_PASS != PREMISE_DISCHARGE
```

| B-tier parent | Present native body | Remaining exact obligation |
|---|---|---|
| NP01 | `SameFlowAt`, `SameMetricAt`, independent quotient carriers | Full analytic restriction and lift/decode descent |
| NP02 | Actual cosine Poisson series, Leray formula, constant/zero actions | Analytic convergence, inversion, zero-mode identities and derivative commutation |
| NP03 | Actual tensor source, scalar correction, signed trace reversal, Hamiltonian and initial K00 identities | Full differential conservation and scalar normal-form analytic interfaces |
| NP04 | Zero actual tensor stress implies actual local NSE under `GeometricReconstructionLaws` | Derive the exact reconstruction identity from Gaussian vacuum |
| NP05 | `completedBoundary` and explicit normalized scalar-completion certificate | Inhabitant of `ScalarBoundaryCompletionLaws` |
| NP06 | Actual inverse/Christoffel/Ricci/Einstein definitions; Lorentzian flat example | General signed Gaussian curvature and Bianchi propagation identities |
| NP07 | Independent constrained-boundary and actual radial-extension result types | Inhabitant of `AnalyticRadialExtensionLaws` |
| NP08 | Actual pressure-gauge equivalence relation and origin-gauge identity | Gauge invariance of the chosen scalar/radial completion |
| NP09 | Sequential forward/reverse functions and conditional quotient equivalence | Inhabitants of all three analytic laws and `GermInverseLaws` |
| NP10 | Exact finite initial block and Hamiltonian K00 solve | Analytic trace recurrence and realized-trace rigidity |
| NP11 | Independent metric constitutive admission, actual STF identities | Full Poisson/Leray/Curl diagnostic theorem |
| NP12 | Exact finite viscosity-affine STF identity | Integrated viscosity recovery and Gram criteria |
| NP13 | Mathematical proof preserved in TXT | Native periodic forced relative-energy proof |
| NP14 | Native flat vacuum and proof of failure of nonzero-rho normalization | Nonzero-rho canonical example and full strictness witnesses |
| NP15 | Positive local radii; interval inclusion and neighborhood lemma | Uniform compact-torus collars and analytic gluing |
| NP16 | Actual ordinary-time derivative and source formulas | Justified differentiated Fourier synthesis and source semantic adapters |

The 153 atomic contracts remain individually specified in the full TXT. Native finite identities cover explicit parts of these parents; no entire parent is marked discharged merely because its definitions or a conditional wrapper compile.

## Executable stage order

1. `GRAdapter`: native semantic and algebra bodies plus explicit actual predicates.
2. `NSEGRForward`: scalar completion certificate → constrained boundary → actual radial vacuum → independent canonical sector.
3. `NSEGRReverse`: actual reconstruction identity + zero constitutive stress → actual local analytic NSE; explicit germ descent/inverse laws → exact equivalence.

Each stage has its own nonempty named audit inventory. Later stage failure preserves earlier-stage build/type/axiom logs. Conditional theorem inputs are retained in the full printed types.

## Frozen unresolved contracts

```lean
ScalarBoundaryCompletionLaws ν ρ t0
AnalyticRadialExtensionLaws ρ t0
GeometricReconstructionLaws ν ρ t0
GermInverseLaws c r h
```

`GermInverseLaws` has two individually visible fields: `forward_respects`, `lift_decode`. No axiom declaration or law inhabitant is introduced.

The decoded-left-inverse identity is derived from exact local boundary matching and pressure-derivative locality (`forward_pressure_gauge_recovery`); it is not an additional `GermInverseLaws` field.

Native metric-jet locality derives reverse descent (`sameMetricAt_boundaryFields`); `reverseGerm` depends only on `GeometricReconstructionLaws`. The analytic pressure-gauge witness is established on the common positive-radius interval.

External certificate: adapter 190/190; forward 6/6; reverse 6/6; standard axioms only. Exact compiled commit `3dc98a61115f8d2e79d115d70b8c3478c504d82e`. Native edges are A_TIER; the root is CONDITIONAL_FORMAL_CLOSURE with the named uninhabited contract packages above.
