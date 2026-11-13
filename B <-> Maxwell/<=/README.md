# Constrained Maxwell ⇒ Fefferman B

```text
DIRECTION                       = MaxwellB → FeffermanB
MATHEMATICAL_STATUS             = B_TIER
RESTRUCTURED_LEAN_SOURCE_STATUS = A_TIER_FOR_EXACT_CONDITIONAL_ENDPOINTS
MATCHING_LAYOUT_COMPILER_AUDIT  = PASS_STANDARD_ONLY
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
- [Concrete statement adapter](../../Fefferman_B_adapter/NSEMaxwell/Classical.lean): exact Fefferman-B predicate and the imported native Maxwell definitions.
- [Common analytic contracts](../../Fefferman_B_adapter/NSEMaxwell/AnalyticContracts.lean): explicit local premises shared by the two directions.

## External certificate

```text
AUDITED_SOURCE_COMMIT  = be8376a08573a7789e36b68c2bc48178aa6f53c3
EXTERNAL_RUN          = 43345557147
ARTIFACT              = 14001701854
COMPILER              = NATIVE_LINUX_LEAN_4.34.0-rc1
NAMED_AUDIT_RESULTS   = 174 / 174 PASS_STANDARD_ONLY
ACTIVE_LEAN_HASH_MATCH = 30 / 30
```

Both reverse endpoints passed matching external compilation and named theorem-level axiom audits. Their axiom sets are contained in `{propext, Classical.choice, Quot.sound}`. The `PeriodicAnalyticLaws` and `FourierHodgeLaws` parameters remain explicit.

[Audit summary](../../Auxillary/evidence/linux-43345557147/audit-summary.json) · [Source manifest](../../Auxillary/evidence/linux-43345557147/source-manifest.json) · [External run](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147)

```text
UNCONDITIONAL_LEAN_H_INHABITANT = NOT_SUPPLIED
PROMOTION_BASIS                = FRESH_EXTERNAL_COMPILER_AND_AXIOM_AUDIT
EXTERNAL_VALIDATION_TARGET    = CACHED_NATIVE_LINUX_LEAN_4.34.0-rc1
```

Native Maxwell implementation: [Maxwell_Endpoint/](../../Maxwell_Endpoint/); physical geometry, Fourier operators, Maxwell predicate, and native witnesses.
