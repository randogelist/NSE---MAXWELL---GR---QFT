# Fefferman B ⇒ constrained Maxwell

```text
DIRECTION                       = FeffermanB → MaxwellB
MATHEMATICAL_STATUS             = B_TIER
RESTRUCTURED_LEAN_SOURCE_STATUS = A_TIER_CANDIDATE
MATCHING_LAYOUT_COMPILER_AUDIT  = PENDING
LEAN_HODGE_PREMISE              = EXPLICIT
```

## Exact conclusion

\[
!\quad
\forall\nu>0\;\forall c>0:\quad
\mathsf{FeffermanB}(\nu)\Longrightarrow\mathsf{MaxwellB}(\nu,c).
\]

Scope: unforced periodic three-dimensional fields; arbitrary velocity mean; periodic NSE pressure; joint `ContDiffOn ℝ ∞` on `[0,∞) × ℝ³`; the frozen Maxwell constitutive relations.

## Active Lean endpoints

| Source | Declaration |
|---|---|
| [NSEMaxwellForward.lean](NSEMaxwellForward.lean) | `NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_periodicAnalyticLaws` |
| [NSEMaxwellForward/Reduced.lean](NSEMaxwellForward/Reduced.lean) | `NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_fourierHodgeLaws` |

Reduced contract:

```lean
(laws : NSEMaxwell.Bridge.FourierHodgeLaws) (ν c : ℝ) :
  NSEMaxwell.Classical.FeffermanB ν →
  NSEMaxwell.Classical.MaxwellB ν c
```

The active construction includes `momentum_zero_of_ns`, `maxwell_of_faraday`, `faraday_of_ns`, and `maxwell_of_ns`. Existing declaration names and concrete hypotheses are retained.

## Data and solution maps

For arbitrary \(m\) and \(B_0\) satisfying `MagneticData`,

\[
a=U_m[B_0]=m+KB_0,
\qquad
\langle a\rangle=m,
\qquad
\operatorname{curl}a=B_0.
\]

For an NSE solution \((u,p)\) with datum \(a\),

\[
\begin{aligned}
B&=\operatorname{curl}u,\\
E&=G_{\nu,m}[B],\\
\rho&=\operatorname{div}G_{\nu,m}[B],\\
J&=c^2\operatorname{curl}B-DG_{\nu,m}[B]\bigl(V_{\nu,m}[B]\bigr).
\end{aligned}
\]

Mean conservation gives \(u=U_m[B]\). The Lamb and curl-curl identities give

\[
B_t=V_{\nu,m}[B]=-\operatorname{curl}G_{\nu,m}[B],
\qquad
E_t=DG_{\nu,m}[B]\bigl(B_t\bigr),
\]

and therefore all four Maxwell equations with the prescribed constitutive fields.

## Derivation and dependencies

- [B_TO_MAXWELL_B_TIER.txt](B_TO_MAXWELL_B_TIER.txt): directional mathematical derivation.
- [Shared Fourier–Hodge derivation](../FOURIER_HODGE_COMPOSITION_B_TIER.txt): C01–C12 discharge the mathematical analytic adapters; C13, §§14.1–14.3 compose the forward map.
- [Concrete statement adapter](../../Fefferman_B_adapter/NSEMaxwell/Classical.lean): exact `FeffermanB`, `MaxwellB`, operators, and solution predicates.
- [Common analytic contracts](../../Fefferman_B_adapter/NSEMaxwell/AnalyticContracts.lean): explicit local premises shared by the two directions.

```text
UNCONDITIONAL_LEAN_H_INHABITANT = NOT_SUPPLIED
RELOCATION_PROOF_PROMOTION     = NONE
EXTERNAL_VALIDATION_TARGET    = CACHED_NATIVE_LINUX_LEAN_4.34.0-rc1
```
