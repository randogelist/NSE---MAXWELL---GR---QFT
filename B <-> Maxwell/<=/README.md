# Constrained Maxwell ⇒ Fefferman B

```text
DIRECTION                       = MaxwellB → FeffermanB
MATHEMATICAL_STATUS             = B_TIER
RESTRUCTURED_LEAN_SOURCE_STATUS = A_TIER_CANDIDATE
MATCHING_LAYOUT_COMPILER_AUDIT  = PENDING
LEAN_HODGE_PREMISE              = EXPLICIT
```

## Exact conclusion

\[
!\quad
\forall\nu>0\;\forall c>0:\quad
\mathsf{MaxwellB}(\nu,c)\Longrightarrow\mathsf{FeffermanB}(\nu).
\]

Scope: unforced periodic three-dimensional fields; arbitrary velocity mean; periodic canonical pressure; joint `ContDiffOn ℝ ∞` on `[0,∞) × ℝ³`; the frozen Maxwell constitutive relations.

## Active Lean endpoints

| Source | Declaration |
|---|---|
| [NSEMaxwellReverse.lean](NSEMaxwellReverse.lean) | `NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_periodicAnalyticLaws` |
| [NSEMaxwellReverse/Reduced.lean](NSEMaxwellReverse/Reduced.lean) | `NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_fourierHodgeLaws` |

Reduced contract:

```lean
(laws : NSEMaxwell.Bridge.FourierHodgeLaws) (ν c : ℝ) :
  NSEMaxwell.Classical.MaxwellB ν c →
  NSEMaxwell.Classical.FeffermanB ν
```

The active construction includes `canonical_momentum_split`, `canonical_momentum_factorization`, `canonical_momentum_zero_of_faraday`, and `ns_of_maxwell`. The optional off-solution factorization retains its own explicit additivity premise; the existence implication uses on-solution cancellation.

## Data and solution maps

For arbitrary `Data a`,

\[
m=\langle a\rangle,
\qquad
B_0=\operatorname{curl}a.
\]

For the corresponding constrained-Maxwell solution,

\[
u=m+KB,
\qquad
h=L(\operatorname{div}G[B]),
\qquad
p=h-\frac{|u|^2}{2}+\frac{\langle|u|^2\rangle}{2}.
\]

Faraday and electric Hodge yield

\[
u_t=-K(\operatorname{curl}G[B])=-G[B]-\nabla h.
\]

The Lamb and curl-curl identities then yield

\[
u_t+(u\cdot\nabla)u+\nabla p
=-\nu\operatorname{curl}B
=\nu\Delta u.
\]

The initial reconstruction gives \(u(0)=a\), with arbitrary \(\langle a\rangle\).

## Derivation and dependencies

- [MAXWELL_TO_B_B_TIER.txt](MAXWELL_TO_B_B_TIER.txt): directional mathematical derivation.
- [Shared Fourier–Hodge derivation](../FOURIER_HODGE_COMPOSITION_B_TIER.txt): C01–C12 discharge the mathematical analytic adapters; C13, §§14.1 and 14.4 compose the reverse map.
- [Concrete statement adapter](../../Fefferman_B_adapter/NSEMaxwell/Classical.lean): exact predicates and cosine-integral definitions.
- [Common analytic contracts](../../Fefferman_B_adapter/NSEMaxwell/AnalyticContracts.lean): explicit local premises shared by the two directions.

```text
UNCONDITIONAL_LEAN_H_INHABITANT = NOT_SUPPLIED
RELOCATION_PROOF_PROMOTION     = NONE
EXTERNAL_VALIDATION_TARGET    = CACHED_NATIVE_LINUX_LEAN_4.34.0-rc1
```
