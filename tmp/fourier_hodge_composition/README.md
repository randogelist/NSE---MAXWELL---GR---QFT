# Fourier–Hodge composition staging

```text
MODE                    = B_TIER_DERIVATION
MATHEMATICAL_DERIVATION  = COMPLETE
LEAN_INTEGRATION        = DEFERRED
NEW_A_TIER_PROMOTION    = NONE
LOCAL_LEAN_EXECUTIONS   = 0
SOURCE_SNAPSHOTS        = 14
SELECTED_DECLARATIONS   = 22
```

## Exact conclusions

\[
!\quad \mathsf{FourierHodgeLaws}.
\]

\[
!\quad \forall\nu>0\;\forall c>0:\quad
\mathsf{FeffermanB}(\nu)\iff\mathsf{MaxwellB}(\nu,c).
\]

Scope: the frozen smooth, unforced, periodic three-dimensional problem; arbitrary velocity mean; periodic pressure; joint `ContDiffOn ℝ ∞` through `t = 0`; exact cosine-integral reconstruction; the specified Maxwell constitutive equations.

The existing externally audited Lean implication remains

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED :
  NSEMaxwell.Bridge.FourierHodgeLaws →
  NSEMaxwell.Classical.ExactEquivalence
```

The B-tier construction of its premise is recorded here. Its Lean implementation and external theorem-level audit are deferred.

## Deliverables

| File | Content |
|---|---|
| [FOURIER_HODGE_COMPOSITION_B_TIER.txt](FOURIER_HODGE_COMPOSITION_B_TIER.txt) | Complete mathematical derivation C01–C13, all four Hodge fields, both root implications |
| [ENDPOINTS.json](ENDPOINTS.json) | 16 core, 4 optional, 1 auxiliary, and 1 reference endpoint; exact signatures, source pins, imports, hashes, direct source URLs, audit boundaries |
| [ENDPOINT_INDEX.md](ENDPOINT_INDEX.md) | Compact declaration/source/status index |
| [INTEGRATION_PLAN.md](INTEGRATION_PLAN.md) | Future adapter contracts, dependency order, external cached Linux promotion gates |
| [SOURCES.md](SOURCES.md) | Source attribution, snapshot paths, byte provenance, dependency boundary |
| [CHECKS.json](CHECKS.json) | Static verification and mathematical review record; no compiler certificate |
| [SHA256SUMS](SHA256SUMS) | Checksums for every other staged file |
| `sources/` | Fourteen byte-exact upstream source snapshots, stored as `.lean.txt` references |

## Composition

\[
\begin{gathered}
\text{cube/torus coefficient transport}
\Longrightarrow\text{derivative symbols and rapid decay}
\Longrightarrow\text{weighted absolute summability},\\
\text{Fourier inversion}
\Longrightarrow\text{exact cosine/multiplier identification}
\Longrightarrow\text{Poisson and commutation identities},\\
\text{uniform time-dependent coefficient bounds}
\Longrightarrow\text{continuous Fourier jets}
\Longrightarrow\text{within derivatives at }t=0
\Longrightarrow\text{joint }C^\infty,\\
\text{H1,H2,H3,H4}
\Longrightarrow\mathsf{FourierHodgeLaws}
\Longrightarrow\mathsf{ExactEquivalence}.
\end{gathered}
\]

Decisive boundary endpoint:

```lean
hasFDerivWithinAt_closure_of_tendsto_fderiv
```

Its application to continuous Fourier jets on the closure of `(0, ∞) × ℝ³` supplies the full Fréchet derivative within the forward half-space. Finite-order induction and `contDiffOn_infty` give the exact required smoothness predicate.

## Source pins

| Source | Commit | Compiler |
|---|---|---|
| Frozen target | `63f53e4c31d09cd1325f032d7456d2d2eb4386b3` | Lean `4.34.0-rc1` |
| Mathlib | `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` | Target dependency |
| Methlib | `e9cf90726b8544a268469ebc8fa6634e9c713e07` | Lean `4.33.0` |
| Methlib's Mathlib dependency | `db584cd6d46c92f209a44c0f1c829460d327499d` | Source dependency |

## Formal boundary

M01, M02, M05, and M07 have retained named audits from the existing target certificate. Additional Mathlib names require later named audits. Methlib declarations are source-port candidates. The snapshots retain their original complete imports; their transitive dependency closure is not staged or certified here.

The `.lean.txt` extension preserves upstream source bytes while keeping the references outside the target Lean module graph. Neither the build configuration nor the active endpoint registry is modified by this staging folder. Future integration must supply the exact adapter bodies and audited `FourierHodgeLaws` inhabitant.

\[
\text{B-tier mathematical derivation}\ne
\text{new externally certified Lean theorem}.
\]

Publication scope: this temporary folder only. Integration and compilation occur subsequently under the existing cached native Linux workflow.
