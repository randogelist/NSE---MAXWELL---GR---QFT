# NSE ↔ normalized marked five-dimensional GR sector

```text
MODE = A_TIER_DERIVATION
STATUS = UNCONDITIONAL_CLOSURE
MARKER = !!!!
BRANCH = codex/gr-adapter
AUDITED_SOURCE_COMMIT = d5231111cbdbe8a9c686b52ae4224554d4fba48a
EXTERNAL_RUN = 43509144981
NAMED_AXIOM_AUDITS = 1549/1549 PASS_STANDARD_ONLY
MATCHING_SOURCE_HASHES = 373/373
FAILED_STAGES = 0
UNRESOLVED_NATIVE_TARGETS = 0
UNRESOLVED_LITERATURE_INPUTS = empty
UNRESOLVED_PROJECT_LAWS = empty
LOCAL_LEAN_EXECUTIONS = 0
```

## Exact root

```lean
NSEGR.NativeLiterature.NSE_GR_NATIVE_LITERATURE_CLOSURE :
  ∀ (ν ρ t0 : ℝ),
    0 < ν → ρ ≠ 0 → NSEGR.ExactSectorEquivalence ν ρ t0

-- ExactSectorEquivalence ν ρ t0
-- = Nonempty (NSEGR.NSEgerm ν t0 ≃ NSEGR.GRgerm ν ρ t0)
```

\[
\boxed{\forall\nu>0\;\forall\rho\ne0\;\forall t_0\in\mathbb R,\quad
\operatorname{Nonempty}\!\left(
\mathrm{NSEgerm}_{\nu,t_0}\simeq\mathrm{GRgerm}_{\nu,\rho,t_0}\right).}
\]

[Root source](../ASSEMBLY/GRAssembly/NSE_GR_NATIVE_LITERATURE_CLOSURE.lean) ·
[A-tier report](../Auxillary/GR/Closure/Native/NSE_GR_NATIVE_LITERATURE_CLOSURE_A_TIER.txt) ·
[External certificate](../Auxillary/GR/Closure/Native/EXTERNAL_CERTIFICATE.json)

## Carrier definitions

| Component | Exact scope |
|---|---|
| `NSEgerm ν t0` | Local jointly real-analytic unforced incompressible three-dimensional NSE; unit spatial periodicity; ordinary time near `t0` |
| `SameFlowAt` | Full-spatial-slice velocity equality; spatially constant pressure difference; equality eventually in time |
| `GRgerm ν ρ t0` | Local jointly real-analytic five-dimensional Lorentzian vacuum metrics; fixed Gaussian marking; unit spatial periodicity; positive time and radial collar widths |
| Gaussian marking | `g_rr = 1`; `g_ra = 0`; induced boundary metric `eta4`; fixed positive radial orientation |
| Boundary normalization | `boundaryBeta (boundaryK g) t0 x = ρ`; `∂t boundaryBeta (boundaryK g) t0 x = 0`; `ρ ≠ 0` |
| Constitutive sector | `∀ t ∈ timeInterval t0 δ, ∀ x, boundaryStress ν (boundaryK g) t x = 0` |
| `SameMetricAt` | Metric equality on a common radial/time neighborhood, uniformly over every spatial point, in the fixed marking |
| Geometric operators | Actual coordinate derivatives, metric inverse, Christoffel symbols, Ricci tensor and metric boundary jet |

\[
K=\operatorname{boundaryK}(g),\qquad
\operatorname{Ric}(g)=0,\qquad
\operatorname{boundaryStress}_{\nu}(K)=0.
\]

```text
SOURCE_CARRIER = GRAdapter/Germs.lean : NSEgerm
TARGET_CARRIER = GRAdapter/Germs.lean : GRgerm
TARGET_SECTOR = GRAdapter/Sector.lean : CanonicalRepresentative
CARRIER_DEFINITIONS = INDEPENDENT
THEOREM_SCOPE = LOCAL_ANALYTIC_GERM_EQUIVALENCE
GLOBAL_FEFFERMAN_B_CLAIM = NONE
GENERAL_FOUR_DIMENSIONAL_GR_CLAIM = NONE
```

[NSE fields](GRAdapter/Fields.lean) · [Metric sector](GRAdapter/Sector.lean) ·
[Germ quotients](GRAdapter/Germs.lean) · [Boundary operators](GRAdapter/Boundary.lean)

## Discharged literature inputs

| Input | Native inhabitant | Status |
|---|---|---|
| `LiteratureAnalyticCKInput` (`LI01`) | `NSEGR.NativeLiterature.literatureAnalyticCKInput_native` | `A_TIER; PASS_STANDARD_ONLY` |
| `LiteratureGaussianJetInput` (`LI02`) | `NSEGR.NativeLiterature.literatureGaussianJetInput_native` | `A_TIER; PASS_STANDARD_ONLY` |
| `LiteratureSmoothFourierInput` (`LI03`) | `NSEGR.NativeLiterature.literatureSmoothFourierInput_native` | `A_TIER; PASS_STANDARD_ONLY` |
| `LiteratureInputs` | `NSEGR.NativeLiterature.literatureInputs_native` | `A_TIER; PASS_STANDARD_ONLY` |

\[
\mathrm{native\ CK}\Longrightarrow\mathrm{native\ Gaussian\ jet},\qquad
(\mathrm{LI01}_{\rm native},\mathrm{LI02}_{\rm native},\mathrm{LI03}_{\rm native})
\Longrightarrow\mathrm{ExactSectorEquivalence}.
\]

```text
ROOT_LITERATURE_INPUT_ARGUMENTS = 0
ROOT_PROJECT_LAW_ARGUMENTS = 0
ROOT_PARAMETER_HYPOTHESES = {0 < ν, ρ ≠ 0}
ROOT_AXIOMS = {propext, Classical.choice, Quot.sound}
sorryAx = absent
NEW_AXIOMS = 0
```

## Matching external evidence

| Field | Value |
|---|---|
| External execution | [GitHub Actions 43509144981](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43509144981) |
| Audited source | `d5231111cbdbe8a9c686b52ae4224554d4fba48a` |
| Compiler | Lean `4.34.0-rc1`; native `x86_64-unknown-linux-gnu` |
| Compiler commit | `3447a668783dbce1a8fdb97101dd067687b2b418` |
| Mathlib commit | `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` |
| Audit mode | `FRESH_BATCH`; exact theorem types and named axiom records |
| Audit inventory | `1549/1549`; `PASS_STANDARD_ONLY` |
| Source inventory | `373/373`; matching bytes |
| Source-manifest SHA-256 | `555bccdb3b8db857077fdd41f409e1c8135933bb1f4bdd6e1366a0c48b747734` |

[Original external artifact](../Auxillary/GR/Closure/Native/evidence/d5231111cbdbe8a9c686b52ae4224554d4fba48a/original-artifact.zip)

```text
BUILD_POLICY = CACHED_EXTERNAL_NATIVE_ONLY
CACHE_DELETION = forbidden
AUDIT_PROMOTION = MATCHING_COMPILER + EXACT_ROOT_TYPE + NAMED_AXIOMS + PREMISE_DISCHARGE
POST_CERTIFICATE_README_CHANGE = DOCUMENTATION_ONLY
AUDITED_PROOF_INPUT_CHANGE = 0
```

## Historical provenance

[Previous GR README — exact preserved bytes](../Auxillary/GR/Closure/Native/HISTORICAL_GR_README.md)

```text
HISTORICAL_README_STATUS = PRIOR_CONDITIONAL_MILESTONES
CURRENT_ROOT_STATUS = UNCONDITIONAL_CLOSURE
CURRENT_ROOT_EVIDENCE = d5231111cbdbe8a9c686b52ae4224554d4fba48a / 43509144981
```
