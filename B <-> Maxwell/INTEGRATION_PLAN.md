# Fourier–Hodge integration record

```text
CANONICAL_ROOT = NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL
ROOT_TYPE = NSEMaxwell.Classical.ExactEquivalence
STATE = UNCONDITIONAL_CLOSURE
EXTERNAL_RUN = 43373061238
CERTIFIED_SOURCE = c4c7bcdca6e652905107bb1a3102ed50d94c2e6b
AUDITS = 400 integrated / 400 isolated Fefferman / 62 isolated Maxwell
COMPILER = external native Linux / Lean 4.34.0-rc1
LOCAL_LEAN_EXECUTIONS = 0
```

This record identifies the native implementation of the obligations derived in [FOURIER_HODGE_COMPOSITION_B_TIER.txt](FOURIER_HODGE_COMPOSITION_B_TIER.txt). The mathematical derivation is retained unchanged. The original conditional APIs remain available; the canonical root supplies their proved four-field inhabitant.

## 1. Native source identity and scope

The 19 files in `Fefferman_adapter/FourierHodgeLaws/` and `Fefferman_adapter/FourierHodgeLaws_inhabitant.lean` are byte-identical to the original Methlib source at `f927f1e31196f0be71b2581dc85f6e3fd19e0746`. All 163 Hodge theorem declarations are included in the named audit inventory. One repository-level canonical wrapper raises the original 236-target inventory to 400.

The selected older `SingularClosure` dependency closure remains 39 native modules from Methlib `e9cf90726b8544a268469ebc8fa6634e9c713e07`. Its target-compiler endpoint certificate is run 43359539373. Its original Lean version and the historical `.lean.txt` reference copies do not change the compiler used to validate the current Hodge source.

The frozen target preserves `EuclideanSpace ℝ (Fin 3)`, the actual cube and volume measure, the all-frequency cosine normalization, arbitrary velocity mean, periodic pressure, and joint smoothness through zero. The target is not replaced by an adjusted mean-zero global-existence proposition.

## 2. Spatial proof chain

All unqualified theorem names in this section belong to `NSEMaxwell.HodgeProof`.

| Native module | Concrete endpoint or role | Mathematical derivation |
|---|---|---|
| `TargetPrimitives` | Actual cube coefficients, inverse multiplier, native source adapters | C01–C03 |
| `FourierCoefficients` | `scalarCoeff_coordinateDerivative`, rapid coefficient decay, inverse-coefficient weighted summability | C02–C03 |
| `CosineMultiplier` | `scalarL_eq_realFourierSeries`, `vectorL_eq_smoothFourierSynthesis`, `vectorL_component`, actual spatial smoothness | C04–C06 |
| `SpatialMultiplier` | `coordinateDerivative_vectorL_commute`, `divergence_vectorL_commute`, `curl_vectorL_commute` | C06 |
| `PoissonFromCoefficients` | `neg_laplacian_vectorL` | C06 |
| `SpatialHodge` | Curl-curl reconstruction, actual means, general Hodge identities | C07 |
| `ElectricHodge` | Actual electric-field mean identity and electric Hodge assembly | C10 |
| `SpatialInhabitant` | `spatialInverseLaplacianLaws`, H1, H2, H4 | C07–C10 |

Linearity and termwise calculus use the smooth periodic class and proved summability. No unrestricted linearity of a totalized nonsummable `tsum` is assumed. The coordinate-volume transport preserves the frozen Euclidean norm and measure.

## 3. Parameter and boundary proof chain

| Native module | Concrete endpoint or role | Exact retained boundary |
|---|---|---|
| `ParameterIntegral` | `scalarMean_trajectory_smooth`, `kineticMean_trajectory_smooth` | Actual cube mean; all nonnegative times |
| `ParameterCoefficients` | `scalarCoeff_hasDerivWithinAt`, `scalarCoeff_contDiffOn`, smooth time/spatial derivative trajectories | Actual `derivWithin` on `Ici 0` |
| `UniformCoefficientBounds` | `uniform_inverseScalarCoeff_moment_bound` and native coefficient bounds | Arbitrary compact nonnegative time intervals |
| `ClosedHalfspaceSmooth` | `hasFDerivWithinAt_closure_of_continuous_jets` | Full derivative within the closed forward half-space |
| `ParameterJets` | Generic summable jet calculus | Explicit summability hypotheses discharged by coefficient bounds |
| `ParameterSmoothing` | `scalarL_trajectory_smooth`, `vectorL_trajectory_smooth` | Joint `ContDiffOn ℝ ∞` through `t = 0` |
| `CanonicalSmoothness`, `CanonicalFromScalar`, `CanonicalInhabitant` | `canonical_smoothness`, `h3_canonical_smoothness` | Actual velocity, pressure, and divergence-free assertions |

The actual parameter-smoothing proof establishes continuity of the Fourier sum and its derivative on compact slabs, differentiates on positive-time spacetime, extends the derivative to the closed half-space, and inducts over finite smoothness orders before passing to infinity. Its scalar/vector smoothing endpoints require only joint smoothness and spatial periodicity. No divergence-free, mean-zero, analyticity, or negative-time extension premise is added.

## 4. Final endpoints and deterministic composition

| Field | Native theorem | Preserved hypothesis or conclusion |
|---|---|---|
| H1: `reconstruct_velocity` | `h1_reconstruct_velocity` | Every `Data a`; reconstruction uses the actual arbitrary mean |
| H2: `reconstruct_curl` | `h2_reconstruct_curl` | Every `MagneticData B`; independent arbitrary `m` |
| H3: `canonical_smoothness` | `h3_canonical_smoothness` | Every `MagneticPath B`; all three canonical smoothness fields |
| H4: `electric_hodge` | `h4_electric_hodge` | Exact `headPotential = scalarL (div G)` and plus-gradient sign |

```lean
NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant :
  NSEMaxwell.Bridge.FourierHodgeLaws

NSEMaxwell.HodgeProof.exact_equivalence_native :
  NSEMaxwell.Classical.ExactEquivalence

NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL :
  NSEMaxwell.Classical.ExactEquivalence
```

`fourierHodgeLaws_inhabitant` assembles H1–H4. `exact_equivalence_native` applies the existing exact reduction to this inhabitant. The canonical wrapper is that exact native equivalence theorem. No analytic-law argument remains in the root signature.

## 5. Matching external certificate

[Run 43373061238](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43373061238), source `c4c7bcdca6e652905107bb1a3102ed50d94c2e6b`, passed native compilation, source verification, package isolation, and fresh named theorem audits: 400 integrated, 400 isolated Fefferman, and 62 isolated Maxwell targets. [Matching evidence](../Auxillary/evidence/linux-43373061238) records the exact inputs and results.

Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The original Methlib Hodge certificate and prior 236-target repository certificates retain their original source/run scope. Existing compiler and dependency caches are reused only after pin and Lake trace verification; theorem audits execute fresh. No old evidence file is replaced.

## 6. Mathematical conclusion

```text
EXACT_EQUIVALENCE = PROVED
FOURIER_HODGE_FIELDS_H1_H2_H3_H4 = DISCHARGED
ROOT_CERTIFICATE_WITNESS_CHECKER_ADMISSION_ANALYTIC_PREMISES = NONE
ARBITRARY_DATA_FEFFERMAN_B_EXISTENCE = OPEN
ARBITRARY_DATA_MAXWELL_B_EXISTENCE = OPEN
```

Unconditional closure applies to the exact equivalence. The root retains its quantified positive viscosity and positive wave-speed parameters and proves both implications. Neither arbitrary-data existence proposition is asserted independently.
