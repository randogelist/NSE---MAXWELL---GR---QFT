# Selected public endpoint index

```text
CORE = 16
OPTIONAL = 4
AUXILIARY = 1
REFERENCE_ONLY = 1
TOTAL = 22
```

Exact signatures, implicit context, required adapters and source imports: [ENDPOINTS.json](ENDPOINTS.json). Mathematical composition: [FOURIER_HODGE_COMPOSITION_B_TIER.txt](FOURIER_HODGE_COMPOSITION_B_TIER.txt).

## Declaration index

| ID | Declaration | Selection | Source snapshot | Target audit status |
|---|---|---|---|---|
| M01 | [`UnitAddTorus.mFourierCoeff_eq_integral`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean#L251) | core | [AddCircleMulti.lean](sources/mathlib/Mathlib/Analysis/Fourier/AddCircleMulti.lean.txt) | Retained named audit: standard axioms only |
| M02 | [`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean#L329) | core | [AddCircleMulti.lean](sources/mathlib/Mathlib/Analysis/Fourier/AddCircleMulti.lean.txt) | Retained named audit: standard axioms only |
| M03 | [`UnitAddTorus.mFourierBasis_repr`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean#L276) | core | [AddCircleMulti.lean](sources/mathlib/Mathlib/Analysis/Fourier/AddCircleMulti.lean.txt) | Pinned source; new named audit deferred |
| M04 | [`ContinuousMap.toLp_injective`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean#L178) | core | [ContinuousFunctions.lean](sources/mathlib/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean.txt) | Pinned source; new named audit deferred |
| M05 | [`ZLattice.summable_norm_pow_inv`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Algebra/Module/ZLattice/Summable.lean#L273) | core | [Summable.lean](sources/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean.txt) | Retained named audit: standard axioms only |
| M06 | [`hasFDerivAt_tsum_of_isPreconnected`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/SmoothSeries.lean#L72) | core | [SmoothSeries.lean](sources/mathlib/Mathlib/Analysis/Calculus/SmoothSeries.lean.txt) | Pinned source; new named audit deferred |
| M07 | [`contDiff_tsum`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/SmoothSeries.lean#L225) | core | [SmoothSeries.lean](sources/mathlib/Mathlib/Analysis/Calculus/SmoothSeries.lean.txt) | Retained named audit: standard axioms only |
| M08 | [`hasFDerivWithinAt_closure_of_tendsto_fderiv`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/FDeriv/Extend.lean#L36) | core | [Extend.lean](sources/mathlib/Mathlib/Analysis/Calculus/FDeriv/Extend.lean.txt) | Pinned source; new named audit deferred |
| M09 | [`contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L875) | core | [Defs.lean](sources/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean.txt) | Pinned source; new named audit deferred |
| M10 | [`contDiffOn_infty`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L549) | core | [Defs.lean](sources/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean.txt) | Pinned source; new named audit deferred |
| M11 | [`contDiffOn_of_locally_contDiffOn`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L587) | optional localization | [Defs.lean](sources/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean.txt) | Pinned source; new named audit deferred |
| M12 | [`UnitAddTorus.mFourierCoeff_toLp`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean#L312) | auxiliary exact injectivity chain | [AddCircleMulti.lean](sources/mathlib/Mathlib/Analysis/Fourier/AddCircleMulti.lean.txt) | Pinned source; new named audit deferred |
| T01 | [`SingularClosure.torusDatumComponent_fourierCoeff`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierRealization.lean#L137) | core | [PeriodicFourierRealization.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierRealization.lean.txt) | Source-port candidate; target audit deferred |
| T02 | [`SingularClosure.datumFourierCoeff_coordinateDerivative`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InitialCutoffBounds.lean#L130) | core | [InitialCutoffBounds.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InitialCutoffBounds.lean.txt) | Source-port candidate; target audit deferred |
| T03 | [`SingularClosure.FOURIER_POLYNOMIAL_DECAY`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierDecay.lean#L162) | core | [FourierDecay.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierDecay.lean.txt) | Source-port candidate; target audit deferred |
| T04 | [`SingularClosure.scalarFourierSeries_contDiff`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierSeriesCalculus.lean#L149) | core | [FourierSeriesCalculus.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierSeriesCalculus.lean.txt) | Source-port candidate; target audit deferred |
| T05 | [`SingularClosure.scalarFourierSeries_coefficient`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean#L210) | core | [SobolevSmoothRealization.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean.txt) | Source-port candidate; target audit deferred |
| T06 | [`SingularClosure.datumFourierCoeff_injective_continuous_periodic`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierInjective.lean#L77) | core | [PeriodicFourierInjective.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierInjective.lean.txt) | Source-port candidate; target audit deferred |
| T07 | [`SingularClosure.infiniteTransportPressure_recovery`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InfiniteFourierPressure.lean#L158) | optional pressure route | [InfiniteFourierPressure.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InfiniteFourierPressure.lean.txt) | Source-port candidate; target audit deferred |
| T08 | [`SingularClosure.datumFourierCoeff_smoothFourierSynthesis`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean#L246) | optional real synthesis | [SobolevSmoothRealization.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean.txt) | Source-port candidate; target audit deferred |
| T09 | [`SingularClosure.smoothFourierSynthesis_coordinateDerivative`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean#L112) | optional real synthesis | [SobolevSmoothRealization.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean.txt) | Source-port candidate; target audit deferred |
| T10 | [`SingularClosure.summable_torusSobolevWeight_inv_four`](https://github.com/randogelist/Methlib/blob/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/LatticeSobolevSummability.lean#L66) | reference only lattice helper | [LatticeSobolevSummability.lean](sources/methlib/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/LatticeSobolevSummability.lean.txt) | Source-port candidate; target audit deferred |

## Mathematical role

### M01 — `UnitAddTorus.mFourierCoeff_eq_integral`

Identify normalized torus Fourier integrals with the physical cube integrals after Euclidean/Pi measure transport and Icc/Ioc null-boundary alignment.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean)

### M02 — `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`

Reconstruct a continuous periodic field pointwise after absolute summability has been proved.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean)

### M03 — `UnitAddTorus.mFourierBasis_repr`

Fourier coefficient equality implies L2 equality by injectivity of the Hilbert-basis representation.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean)

### M04 — `ContinuousMap.toLp_injective`

Upgrade continuous torus Lp equality to pointwise equality under Haar full support.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean)

### M05 — `ZLattice.summable_norm_pow_inv`

Supply summable nonzero-frequency inverse powers with exponent greater than dimension three.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Algebra/Module/ZLattice/Summable.lean)

### M06 — `hasFDerivAt_tsum_of_isPreconnected`

Differentiate Fourier jet series on each open convex time slab using uniform summable derivative bounds.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/SmoothSeries.lean)

### M07 — `contDiff_tsum`

Establish spatial C-infinity of Fourier synthesis from bounds for every iterated derivative.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/SmoothSeries.lean)

### M08 — `hasFDerivWithinAt_closure_of_tendsto_fderiv`

Extend the actual Fréchet derivative of each Fourier jet from the positive-time interior to the closed forward spacetime.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/FDeriv/Extend.lean)

### M09 — `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`

Prove all finite ContDiffOn orders by induction on continuous compatible derivative jets.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean)

### M10 — `contDiffOn_infty`

Pass from all finite ContDiffOn orders to ContDiffOn infinity.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean)

### M11 — `contDiffOn_of_locally_contDiffOn`

Glue time-local ContDiffOn conclusions on relatively open neighborhoods if the integration proof uses bounded slabs.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean)

### M12 — `UnitAddTorus.mFourierCoeff_toLp`

Transport actual continuous torus Fourier coefficients to the L2 representative before applying Hilbert-basis representation injectivity.

[Direct upstream download](https://raw.githubusercontent.com/leanprover-community/mathlib4/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Fourier/AddCircleMulti.lean)

### T01 — `SingularClosure.torusDatumComponent_fourierCoeff`

Source-port template for actual Euclidean cube coefficient transport.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierRealization.lean)

### T02 — `SingularClosure.datumFourierCoeff_coordinateDerivative`

Source-port template for the spatial derivative coefficient multiplier; compose to obtain divergence, curl, and Laplacian multipliers.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InitialCutoffBounds.lean)

### T03 — `SingularClosure.FOURIER_POLYNOMIAL_DECAY`

Source-port template for arbitrary polynomial coefficient decay from smoothness and periodicity.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierDecay.lean)

### T04 — `SingularClosure.scalarFourierSeries_contDiff`

Source-port template for scalar smooth Fourier synthesis from weighted absolute summability.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierSeriesCalculus.lean)

### T05 — `SingularClosure.scalarFourierSeries_coefficient`

Recover scalar synthesis coefficients by an absolutely justified integral/tsum interchange and character orthogonality.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean)

### T06 — `SingularClosure.datumFourierCoeff_injective_continuous_periodic`

Source-port template for injectivity on continuous periodic real vector fields without an absolute-summability hypothesis.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierInjective.lean)

### T07 — `SingularClosure.infiniteTransportPressure_recovery`

Alternative electric reconstruction route through actual pressure and coefficient Leray projection.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InfiniteFourierPressure.lean)

### T08 — `SingularClosure.datumFourierCoeff_smoothFourierSynthesis`

Optional shortcut for vector coefficient recovery after proving spectral conjugate symmetry.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean)

### T09 — `SingularClosure.smoothFourierSynthesis_coordinateDerivative`

Optional shortcut for spatial differentiation of the real vector synthesis.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SobolevSmoothRealization.lean)

### T10 — `SingularClosure.summable_torusSobolevWeight_inv_four`

Reference implementation of the lattice embedding, rank-three calculation, zero-frequency repair, and fourth-power summability.

[Direct upstream download](https://raw.githubusercontent.com/randogelist/Methlib/e9cf90726b8544a268469ebc8fa6634e9c713e07/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/LatticeSobolevSummability.lean)

## Formal boundary

The retained named audit applies to the four stated Mathlib declarations at the target pin. No source-package proof status is transferred from Methlib. All new adapters, additional named audits, and the final `FourierHodgeLaws` inhabitant remain deferred integration work.
