# Fefferman B ⇒ constrained Maxwell

```text
DIRECTION                       = FeffermanB → MaxwellB
MATHEMATICAL_STATUS             = B_TIER
RESTRUCTURED_LEAN_SOURCE_STATUS = A_TIER_FOR_EXACT_CONDITIONAL_ENDPOINTS
MATCHING_LAYOUT_COMPILER_AUDIT  = PASS_STANDARD_ONLY
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
- [Concrete statement adapter](../../Fefferman_adapter/NSEMaxwell/Classical.lean): exact `FeffermanB` and the imported native Maxwell definitions.
- [Common analytic contracts](../../Fefferman_adapter/NSEMaxwell/AnalyticContracts.lean): explicit local premises shared by the two directions.

## External certificate

```text
AUDITED_SOURCE_COMMIT  = be8376a08573a7789e36b68c2bc48178aa6f53c3
EXTERNAL_RUN          = 43345557147
ARTIFACT              = 14001701854
COMPILER              = NATIVE_LINUX_LEAN_4.34.0-rc1
NAMED_AUDIT_RESULTS   = 174 / 174 PASS_STANDARD_ONLY
ACTIVE_LEAN_HASH_MATCH = 30 / 30
```

Both forward endpoints passed matching external compilation and named theorem-level axiom audits. Their axiom sets are contained in `{propext, Classical.choice, Quot.sound}`. The `PeriodicAnalyticLaws` and `FourierHodgeLaws` parameters remain explicit.

[Audit summary](../../Auxillary/evidence/linux-43345557147/audit-summary.json) · [Source manifest](../../Auxillary/evidence/linux-43345557147/source-manifest.json) · [External run](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147)

```text
UNCONDITIONAL_LEAN_H_INHABITANT = NOT_SUPPLIED
PROMOTION_BASIS                = FRESH_EXTERNAL_COMPILER_AND_AXIOM_AUDIT
EXTERNAL_VALIDATION_TARGET    = CACHED_NATIVE_LINUX_LEAN_4.34.0-rc1
```

Native Maxwell implementation: [Maxwell_Endpoint/](../../Maxwell_Endpoint/); physical geometry, Fourier operators, Maxwell predicate, and native witnesses.
