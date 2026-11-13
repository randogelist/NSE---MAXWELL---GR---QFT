# Quantum-adapter endpoint index

`STATUS = A_TIER_CANDIDATE` for the native declarations below until matching external compilation and theorem-level axiom-audit evidence exists. `SOURCE_VERIFIED` denotes inspection of the pinned upstream declaration; it does not denote successful elaboration of the new caller. No local Lean execution is part of this index.

`SCOPE =` actual arbitrary-mean Fourier phase, actual finite drift, actual Gaussian functions, actual Born expectations, conditional complex-L2 transport, and ordered conditional regularity implications.

## Source pins

| Register | Exact source | Role |
|---|---|---|
| `ML` | Mathlib [`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`](https://github.com/leanprover-community/mathlib4/tree/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11), Lean `4.34.0-rc1` target | Active upstream endpoint register below. |
| `ME` | Repository snapshot [`1de664f2ef5ddc11caef25ac2274278b4171ab6b`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/tree/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure), prefix `Fefferman_adapter/NativeSources/methlib/SingularClosure/` | Exact vendored Methlib sources inspected; identities refer to this repository snapshot. |
| `TXT` | B-tier v1.8.0: Lean `4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`; Methlib `09dfe94a1ef150e21d09df3013fbe09002ef139c` | Historical prospective checkpoint register. Not interchangeable with `ML` or `ME`. |

The tables record selected directly used semantic endpoints, not the transitive import closure or every tactic/typeclass dependency. `Native` entries refer to declarations in this branch; `ML` and `ME` entries refer to existing pinned sources.

## Existing Mathlib endpoints

Implicit typeclass parameters retain their upstream signatures. The contracts below display the hypotheses material to the native use.

| ID | Exact existing declaration and pinned source | Contract used |
|---|---|---|
| `ML01` | [`stdOrthonormalBasis`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L1076) | Finite-dimensional inner-product space `E` over `𝕜` → `OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E`. |
| `ML02` | [`Module.Basis.addHaar`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean#L255); [`isAddHaarMeasure_basis_addHaar`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean#L258); [anonymous `SigmaFinite` instance](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean#L261) | Finite real basis, normed-space and Borel instances → intrinsic Haar measure, sigma finite. |
| `ML03` | [`Submodule.orthogonalProjectionOnto`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L113) | `[K.HasOrthogonalProjection]` → `E →L[𝕜] K`. |
| `ML04` | [`Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L227) | `v : K` → `K.orthogonalProjectionOnto v = v`. The source uses `orthogonalProjectionOnto`, not a guessed legacy signature. |
| `ML05` | [`ContinuousLinearMap.hasFDerivAt`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/FDeriv/Linear.lean#L57) | Continuous linear map `f` → `HasFDerivAt f f x`. |
| `ML06` | [`real_inner_comm`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/InnerProductSpace/Basic.lean#L59); [`real_inner_self_eq_norm_sq`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/InnerProductSpace/Basic.lean#L396) | Real-inner-product symmetry; `inner ℝ x x = ‖x‖²`. |
| `ML07` | [`Complex.normSq_ofReal`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Data/Complex/Basic.lean#L521); [`Complex.normSq_nonneg`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Data/Complex/Basic.lean#L555); [`Complex.normSq_mul`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Data/Complex/Basic.lean#L574) | Real-cast square, nonnegative Born density, multiplicative Born density. |
| `ML08` | [`Complex.normSq_eq_norm_sq`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/Norm.lean#L147) | `Complex.normSq z = ‖z‖²`. |
| `ML09` | [`Real.exp_add`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/Exponential.lean#L211) | `exp (x+y) = exp x * exp y`. |
| `ML10` | [`Real.rpow_pos_of_pos`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L116) | `0 < x` → `0 < x ^ y`. |
| `ML11` | [`MeasureTheory.integral_congr_ae`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L299) | `f =ᵐ[μ] g` → equal Bochner integrals. |
| `ML12` | [`MeasureTheory.integral_const_mul`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L288) | `∫ r*f = r*∫ f` for real/complex scalar functions. |
| `ML13` | [`MeasureTheory.integral_add`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L237); [`MeasureTheory.integral_mono`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L635) | Both summands/comparands integrable; monotonicity additionally requires pointwise order. |
| `ML14` | [`MeasureTheory.integral_nonneg`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L612) | Pointwise nonnegative integrand → nonnegative totalized integral. This endpoint alone supplies no integrability. |
| `ML15` | [`MeasureTheory.memLp_two_iff_integrable_sq_norm`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/L2Space.lean#L45) | `AEStronglyMeasurable f μ` → `(MemLp f 2 μ ↔ Integrable (fun x => ‖f x‖²) μ)`. |
| `ML16` | [`MeasureTheory.L2.inner_def`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/L2Space.lean#L137) | For actual L2 elements: Hilbert inner product equals the integral of pointwise inner products. |
| `ML17` | [`MeasureTheory.MemLp.toLp`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L106); [`MeasureTheory.MemLp.coeFn_toLp`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L111) | `hf : MemLp f p μ` → `hf.toLp f : Lp E p μ`, with representative equal to `f` almost everywhere. |
| `ML18` | [`MeasureTheory.MemLp.toLp_congr`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L115); [`MeasureTheory.MemLp.toLp_sub`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L134) | AE-equivalent MemLp representatives give identical Lp elements; representative subtraction matches quotient subtraction. |
| `ML19` | [`MeasureTheory.Lp.toLp_coeFn`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L167); [`MeasureTheory.Lp.eq_zero_iff_ae_eq_zero`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L304) | Reconstructing an Lp element from its representative returns that element; quotient zero is equivalent to AE-zero representative. |
| `ML20` | [`MeasureTheory.Lp.coeFn_add`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L198); [`MeasureTheory.Lp.coeFn_smul`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L436) | Lp representative addition/scalar multiplication hold almost everywhere. |
| `ML21` | [`LinearIsometryEquiv.ofLinearIsometry`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean#L962) | Linear isometry `f`, linear inverse `g`, and both composition identities → linear isometric equivalence. |
| `ML22` | [`PiLp.proj`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Normed/Lp/PiLp.lean#L1167) | Actual coordinate evaluation as a continuous linear map `PiLp p β →L[𝕜] β i`. |
| `ML23` | [`HasFDerivAt.comp_hasDerivWithinAt`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/Deriv/Comp.lean#L378) | Fréchet derivative of outer map plus within-derivative of curve → within-derivative of the composition. |
| `ML24` | [`antitoneOn_of_hasDerivWithinAt_nonpos`](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean#L496) | Convex real domain, continuity on that domain, and nonpositive within-derivative on its interior → `AntitoneOn`. |

## Existing Methlib endpoints

All names in this table belong to namespace `SingularClosure`. `Frequency`, `Vec`, `Field`, `FourierCoeff`, and the spectral predicates retain the vendored source meanings. These endpoints are not replacements for the exact native `NSEMaxwell.Classical` conclusion.

| ID | Exact existing declaration and pinned source | Contract used |
|---|---|---|
| `ME01` | [`galerkinFreqSq`, `cutoffModes`, `fourierCharacter`, `datumFourierIntegrand`, `datumFourierCoeff`, `finiteSynthesis`, `coefficientLeray`, `coefficientTransport`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/Galerkin.lean#L28) | Actual frequency-square, nonzero cutoff, Fourier integrals, synthesis, Leray projection, finite convolution definitions. Native `fullModes` inserts frequency zero. |
| `ME02` | [`cutoffModes_zero_not_mem`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/Galerkin.lean#L106); [`coefficientLeray_zero`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/Galerkin.lean#L115) | Source cutoff excludes zero; Leray operator maps zero coefficients to zero. |
| `ME03` | [`cutoffModes_neg_mem`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/GalerkinEnergy.lean#L50) | `k ∈ cutoffModes N` → `-k ∈ cutoffModes N`. |
| `ME04` | [`datumFourierCoeff_reality`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L49) | Any real `Field a` → `SpectralReality (datumFourierCoeff a)`. |
| `ME05` | [`datumFourierCoeff_zero`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L59) | `IntegrableOn a unitCube volume` → `datumFourierCoeff a 0 i = (spatialMean a i : ℂ)`. No mean-zero hypothesis. |
| `ME06` | [`datumFourierIntegrand_integrableOn`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L30) | `Continuous a` → integrability of each Fourier integrand on the unit cube. |
| `ME07` | [`datumFourierIntegrand_contDiff`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L162); [`datumFourierIntegrand_periodic`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L174) | Smooth datum → smooth Fourier integrand; spatially periodic datum → spatially periodic Fourier integrand. |
| `ME08` | [`datumFourierIntegrand_coordinateDerivative`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L181) | Differentiable datum → exact product derivative, including `derivativeSymbol i k`. |
| `ME09` | [`integral_unitCube_divergence_eq_zero`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/InitialFourier.lean#L134) | Smooth `f : Fin 3 → Vec → ℂ`, each `f i` periodic in coordinate `i` → integral of summed coordinate derivatives equals zero. |
| `ME10` | [`coefficientLeray_neg_star`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/GalerkinReality.lean#L19) | `coefficientLeray (-k) (fun i => star (v i)) = fun i => star (coefficientLeray k v i)`. |
| `ME11` | [`coefficientTriadPower_swap`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/GalerkinEnergy.lean#L93) | Full coefficient reality and solenoidality at frequency `p` → `coefficientTriadPower c p (p-k) = -coefficientTriadPower c p k`. No zero-mode exclusion occurs in this signature. |
| `ME12` | [`coefficientLeray_pairing`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/GalerkinAlgebra.lean#L250) | Solenoidal `c` at `k` → pairing `star c` against `coefficientLeray k v` equals pairing against `v`. |
| `ME13` | [`complex_viscous_pairing`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/GalerkinAlgebra.lean#L264) | Real part of `star z * (-(lam:ℂ)*z-w)` equals `-lam*normSq z-(star z*w).re`. |
| `ME14` | [`hasDerivWithinAt_complex_normSq`](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/blob/1de664f2ef5ddc11caef25ac2274278b4171ab6b/Fefferman_adapter/NativeSources/methlib/SingularClosure/GalerkinAlgebra.lean#L226) | `HasDerivWithinAt f f' s t` → derivative of `normSq (f t)` equals `2*(star(f t)*f').re`. |

`SingularClosure.smoothSigmaZero_fourier_solenoidal` and `SingularClosure.coefficientTransport_reality` supplied inspected proof patterns, not directly applied endpoints for the new arbitrary-mean/full-cutoff theorems. Their original contracts are not silently enlarged. The unit-cube integration-by-parts endpoint is in `InitialFourier.lean`; no `FourierIBP.lean` source is indexed.

## Native phase and finite-model mappings

All names below have prefix `QuantumAdapter.`. Native source paths are branch-relative.

| Native declarations | Exact mathematical contract / retained premises | Existing endpoints |
|---|---|---|
| [`fullModes_neg_mem`, `fullModes_neg_mem_iff`](QuantumAdapter/Phase.lean) | Negation closure for `insert 0 (cutoffModes N)`; membership premise retained. | `ME03` plus finite-set reductions. |
| [`datumFourierCoeff_solenoidal`](QuantumAdapter/Phase.lean) | `ContDiff ℝ ∞ a`, `SpatialPeriodic a`, and `∀x, divergence a x=0` → `SpectralSolenoidal (datumFourierCoeff a)`. No mean condition. | `ME06`–`ME09`, `ML12`; native Fourier derivative summation. |
| [`initialAmbient_mem`, `initialPhase_coeff`](QuantumAdapter/Phase.lean) | Actual truncated Fourier integrals inhabit the real reality/solenoidality submodule; same smoothness, periodicity and divergence premises. | `ME04`; previous native solenoidality and cutoff closure. |
| [`initialPhase_mean`, `initialPhaseData_mean`](QuantumAdapter/Phase.lean) | Zeroth coefficient equals the datum's actual spatial mean; the latter accepts exactly `NSEMaxwell.Classical.Data a`. | `ME05`; compact-domain integrability from smoothness. |
| [`meanPhase_injective`, `phase_finrank_pos`](QuantumAdapter/Phase.lean) | Constant-vector embedding is injective; every phase has positive real dimension. | Native coefficient evaluation and inherited finite-dimensional structures; no upstream regularity claim. |
| [`energy3_nonneg`, `energy3_zero`](QuantumAdapter/FiniteModel.lean) | Actual weighted finite sum `∑k∈fullModes N,∑i,(1+laplaceSymbol k)^3*normSq(c k i)` is nonnegative; vanishes at zero. | `ML08`; native positive weights and finite sums. |
| [`synthesis_eq_mean_add_source`](QuantumAdapter/FiniteModel.lean) | Full synthesis equals actual mean vector plus vendored nonzero-mode synthesis. | `ME01`, `ME02`. |
| [`fullTransport_eq_source_add_mean`, `fullTransport_eq_source_of_mean_zero`](QuantumAdapter/FiniteModel.lean) | Full convolution equals source convolution plus explicit constant-mean advection; equality to source alone requires `∀i,c 0 i=0`. | `ME01`, `ME02`. |
| [`drift_eq_rawRhs_of_tangent`](QuantumAdapter/FiniteModel.lean) | `h : RawRhsTangent` → `(drift ν N q).val = rawRhs ν N q`. | `ML03`, `ML04`. |
| [`fullTransport_reality`, `coefficientLeray_solenoidal`, `rawRhs_tangent`](QuantumAdapter/Tangency.lean) | Native full-mode conjugation proof and Leray algebra yield actual raw drift membership in the phase submodule. | `ME10`; native full-cutoff negation and finite algebra. |
| [`drift_eq_rawRhs`, `drift_mean`](QuantumAdapter/Tangency.lean) | Actual projected drift equals actual raw RHS; mean coefficient derivative is zero. These declarations require no tangency hypothesis. | Previous native tangency; `ML04` transitively. |
| [`zero_isTrajectory`](QuantumAdapter/FiniteModel.lean) | Zero orbit satisfies the actual `IsTrajectory ν N 0` ODE predicate. It supplies no general flow. | Constant derivative; native `drift_zero`. |
| [`cotangent_momentum_increment`, `cotangent_hasFDerivAt_momentum`, `cotangent_fderiv_momentum`](QuantumAdapter/FiniteModel.lean) | For actual `H(q,p)=inner ℝ p (drift ν N q)`, momentum derivative is `innerSL ℝ (drift ν N q)`. | `ML05`, `ML06`; inner-product linearity. |
| [`fullTransport_complex_energy_zero`](QuantumAdapter/Energy.lean) | Actual full-mode nonlinear energy pairing vanishes, given finite support in `fullModes N`, coefficient reality and solenoidality. | `ME11`; native full-cutoff triad involution. |
| [`fullLerayTransport_complex_energy_zero`, `fullLerayTransport_real_energy_zero`](QuantumAdapter/Energy.lean) | Actual constrained phase supplies the support/reality/solenoidality hypotheses; Leray projection preserves energy cancellation. | `ME12`; previous native cancellation. |
| [`rawRhs_energy_rate`, `rawRhs_energy_rate_nonpos`](QuantumAdapter/Energy.lean) | Actual energy rate equals `(-2*ν)*dissipation N q`; nonpositivity requires `0≤ν`. | `ME13`; native raw-RHS identity and cancellation. |
| [`IsTrajectory.coefficient_hasDerivWithinAt`, `IsTrajectory.energy0_identity`](QuantumAdapter/Energy.lean) | Actual `IsTrajectory ν N q₀ q` and `t≥0` → exact coefficient derivative and unweighted-energy derivative on `Ici 0`. | `ML05`, `ML22`, `ML23`, `ME14`; native tangency and energy rate. |
| [`IsTrajectory.energy0_antitoneOn`, `IsTrajectory.energy0_le_initial`](QuantumAdapter/Energy.lean) | Actual trajectory and `0≤ν` → energy antitone on `Ici 0`; at `t≥0`, `energy0 N (q t)≤energy0 N q₀`. No arbitrary-flow or H3 bound follows. | `ML24`; native dissipation positivity and energy derivative. |

## Native Born, transport, L2 and dynamics mappings

| Native declarations | Exact mathematical contract / retained premises | Existing endpoints |
|---|---|---|
| [`bornDensity_nonneg`, `bornDensity_const_mul`, `bornDensity_unit_phase`](QuantumAdapter/Born.lean) | Actual `normSq` density; unit-phase statement requires `normSq c=1`. | `ML07`. |
| [`WaveAdmissible.toL2`, `WaveAdmissible.coe_toL2`, `WaveAdmissible.expectation_toL2`](QuantumAdapter/Born.lean) | `WaveAdmissible μ ψ` includes actual `MemLp ψ 2 μ` and Born integral `1`; representative and expectation descend by AE equality. | `ML17`, `ML11`. |
| [`expectation_nonneg`, `expectation_const_mul_wave`, `expectation_const`](QuantumAdapter/Born.lean) | Positivity uses nonnegative observable; constant expectation additionally uses normalized admissible state. | `ML07`, `ML11`, `ML12`, `ML14`. |
| [`expectation_mono`, `expectation_add`, `expectation_le_bound`, `bound_le_expectation`](QuantumAdapter/Born.lean) | Actual multiplier-density integrability retained; bounded expectation statements additionally require normalized state and pointwise bound. | `ML13`; native constant expectation. |
| [`halfDensityPullback_zero`, `halfDensityPullback_add`, `halfDensityPullback_inverse`](QuantumAdapter/Transport.lean) | `U(t)ψ(q)=exp(κt/2)ψ(Φ(-t)q)`; zero/group/inverse identities require the displayed zero/group laws of `Φ`. | `ML09`; native algebra. |
| [`bornDensity_halfDensityPullback`](QuantumAdapter/Transport.lean) | `bornDensity (U(t)ψ) q = exp(κt)*bornDensity ψ (Φ(-t)q)`. No measure-transport claim. | `ML07`, `ML09`. |
| [`WaveAdmissible.halfDensityPullback`](QuantumAdapter/Transport.lean) | `IntegralPullbackLaw μ κ Φ`, `MemLpPullbackLaw μ κ Φ`, and initial admissibility → transported admissibility. | `ML11`; explicit native laws remain premises. |
| [`expectation_halfDensityPullback`](QuantumAdapter/Transport.lean) | Zero/group laws, `IntegralPullbackLaw`, and `Integrable (fun q => f (Φ t q)*bornDensity ψ q) μ` → exact observable conjugacy. | `ML11`; explicit change-of-variables law remains a premise. |
| [`memLp_bornDensity_integrable`](QuantumAdapter/L2Norm.lean) | `MemLp ψ 2 μ` → `Integrable (bornDensity ψ) μ`. | `ML15`, `ML08`. |
| [`memLp_toLp_norm_sq`](QuantumAdapter/L2Norm.lean) | `hψ : MemLp ψ 2 μ` → `‖hψ.toLp ψ‖² = ∫q,bornDensity ψ q ∂μ`. | `ML16`, `ML06`, `ML17`, `ML08`, `ML11`. |
| [`WaveAdmissible.norm_toL2`](QuantumAdapter/L2Norm.lean) | Actual admissible state → native L2 norm `1`. | Previous native norm-square identity plus normalization. |
| [`halfDensityPullback_toLp_norm`](QuantumAdapter/L2Norm.lean) | Both transport laws and actual MemLp membership → equality of native L2 norms. | Previous native norm-square/integrability identities; `ML11`. |
| [`halfDensityPullback_congr_ae`](QuantumAdapter/L2Transport.lean) | Both transport laws, MemLp of both waves, and initial AE equality → transported AE equality. | `ML18`, `ML19`; native norm preservation. |
| [`l2Pullback_toLp`, `l2Pullback_norm`, `l2Pullback_add_vectors`, `l2Pullback_smul`](QuantumAdapter/L2Transport.lean) | Both transport laws → actual quotient map agrees with the transformed representative, preserves norm, addition and complex scalar multiplication. | `ML17`–`ML20`; native AE compatibility. |
| [`l2Pullback_zero`, `l2Pullback_add_times`](QuantumAdapter/L2Transport.lean) | Quotient zero/group identities retain the respective flow laws; time-addition also retains both transport laws. | Native representative identities and AE compatibility. |
| [`l2PullbackIsometry`, `l2PullbackEquiv`, `l2PullbackEquiv_apply`, `l2PullbackEquiv_symm_apply`](QuantumAdapter/L2Transport.lean) | Both transport laws → complex linear isometry. Adding zero/group flow laws → `Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ`, inverse at time `-t`. No strong-continuity/generator conclusion. | `ML21`; preceding native quotient theorems. |
| [`phaseVolume`, `phaseVolumeSigmaFinite`](QuantumAdapter/Dynamics.lean) | Intrinsic real Hilbert basis Haar measure on `Phase N`, with sigma finiteness. | `ML01`, `ML02`. |
| [`canonicalScale_pos`, `gaussianAmplitude_pos`, `canonicalPacket_im`, `canonicalPacket_center`, `canonicalPacket_re_pos`](QuantumAdapter/Dynamics.lean) | Positive explicit scale/amplitude; actual Gaussian values. No integral normalization theorem is asserted by these declarations. | `ML10`; native positive phase dimension and explicit formulas. |
| [`transport_zero`, `transport_add`, `transport_inverse`, `transportedPacket_zero`](QuantumAdapter/Dynamics.lean) | Specialization of actual half-density formulas to supplied `F : PhaseFlow ν`. | Native transport algebra. |
| [`phaseFlow_isTrajectory`](QuantumAdapter/Dynamics.lean) | Supplied `PhaseFlow ν` → its orbit satisfies actual `IsTrajectory`; uses its `orbit_derivative` field. | Differentiability-to-continuity/within-derivative conversions; no flow-existence endpoint. |
| [`quantumEnergy_nonneg`](QuantumAdapter/Dynamics.lean) | Actual weighted Born integral is nonnegative; no admissibility follows from this fact. | Native `energy3_nonneg`, `expectation_nonneg`; `ML14` transitively. |
| [`transport_waveAdmissible`, `quantumEnergy_conjugacy`](QuantumAdapter/Dynamics.lean) | Supplied `PhaseTransportLaws F`; admissibility additionally needs initial admissibility; conjugacy additionally needs the displayed integrable transported-observable product. | Native generic transport theorems. |

## Ordered regularity edges

`FB = NSEMaxwell.Classical.FeffermanB ν`; `G = QuantumAdapter.G3 F`; `Q = QuantumAdapter.QREG F`. These are distinct concrete predicates. `Q` includes actual normalized L2 membership, the full multiplication-operator domain, and actual observable integrability, together with cutoff-uniform packet-energy bounds.

| ID | Exact new native theorem | Premises → conclusion | Body dependency |
|---|---|---|---|
| `F1` | [`QuantumAdapter.Directions.feffermanB_implies_galerkin_of_analyticLaws`](../B%20%3C-%3E%20Quantum/%3D%3E/NSEQuantumForward.lean) | `F`, `laws : GalerkinAnalyticLaws F`, `FB` → `G` | Extract native smooth solution; apply `laws.smooth_stability` at each datum/horizon. |
| `F2` | [`QuantumAdapter.Directions.galerkin_implies_quantum_of_packetBounds`](../B%20%3C-%3E%20Quantum/%3D%3E/NSEQuantumForward.lean) | `F`, `Cemb C3`, `packets : PacketBounds F Cemb C3`, `G` → `Q` | `packets.admissible`, per-cutoff `forward_estimate`, native nonnegative explicit bound. |
| `F3` | [`QuantumAdapter.Directions.feffermanB_implies_quantum_of_analyticLaws`](../B%20%3C-%3E%20Quantum/%3D%3E/NSEQuantumForward.lean) | `F`, `Cemb C3`, `laws`, `packets`, `FB` → `Q` | Deterministic `F2 ∘ F1`. |
| `R1` | [`QuantumAdapter.Directions.quantum_implies_galerkin_of_packetBounds`](../B%20%3C-%3E%20Quantum/%3C%3D/NSEQuantumReverse.lean) | `F`, `Cemb C3`, `packets`, `initial : InitialProjectionBounds`, `Q` → `G` | Same datum-wise `A` and horizon-wise `C` at every cutoff; per-cutoff `reverse_estimate`. |
| `R2` | [`QuantumAdapter.Directions.galerkin_implies_feffermanB_of_analyticLaws`](../B%20%3C-%3E%20Quantum/%3C%3D/NSEQuantumReverse.lean) | `F`, `laws`, `G` → `FB` | Fixed-datum `laws.compactness` produces exact native `NSSolution`. |
| `R3` | [`QuantumAdapter.Directions.quantum_implies_feffermanB_of_analyticLaws`](../B%20%3C-%3E%20Quantum/%3C%3D/NSEQuantumReverse.lean) | `F`, `Cemb C3`, `laws`, `packets`, `initial`, `Q` → `FB` | Deterministic `R2 ∘ R1`. |

These six declarations are native proof candidates, not existing Mathlib/Methlib theorems. Their analytic fields are not discharged by importing any endpoint in `ML01`–`ML24` or `ME01`–`ME14`.

The numeric contracts in [`RegularityContracts.lean`](QuantumAdapter/RegularityContracts.lean) are fixed:

```text
forwardPacketBound Cemb T C
  = (sqrt C + (1/2) * exp(Cemb * sqrt C * T))^2

L = Cemb * T * sqrt C
S = L + 1/4
R = sqrt(1/4 + L)
reversePacketBound Cemb C3 T A C
  = ((A + R) * exp(C3*S) + R * exp S)^2
```

`PacketBounds.forward_estimate` requires `N≥1`, `T>0`, `C≥0`, and the central energy bound on `[0,T]`. `reverse_estimate` additionally uses `A≥0`, initial energy `≤A²`, and the packet-energy bound on `[0,T]`. Both constants are independent of `N`. Neither structure field has type `FB → G`, `G → Q`, or `Q → FB`.

The deterministic assembly declarations in [`NSEQuantumBridge.lean`](NSEQuantumBridge.lean) are:

```lean
QuantumAdapter.feffermanB_iff_qreg_of_analytic_bounds
QuantumAdapter.exactQuantumEquivalence_of_analytic_bounds
QuantumAdapter.exact_quantum_conditional_root
```

The root type is exactly:

```lean
∀ ν : ℝ, 0 < ν → ∀ F : QuantumAdapter.PhaseFlow ν, ∀ Cemb C3 : ℝ,
  QuantumAdapter.GalerkinAnalyticLaws F →
  QuantumAdapter.PacketBounds F Cemb C3 →
  QuantumAdapter.InitialProjectionBounds →
  (NSEMaxwell.Classical.FeffermanB ν ↔ QuantumAdapter.QREG F)
```

## Explicit frontier

| Obligation | Present status |
|---|---|
| Actual finite `PhaseFlow` existence and exact divergence identity | Supplied as explicit structure fields; no inhabitant constructed by the regularity assembly. |
| Intrinsic Haar change of variables and L2 pullback membership | Explicit `PhaseTransportLaws`; generic L2 equivalence is conditional on these laws. |
| Gaussian normalization, full multiplier domain and weighted integrability for transported canonical packets | Explicit `PacketBounds.admissible`; positivity and central Gaussian value do not discharge these obligations. |
| Cutoff-independent M11/M13 numerical estimates | Explicit `PacketBounds.forward_estimate` and `reverse_estimate`. |
| Uniform initial Fourier-H3 projection estimate | Explicit `InitialProjectionBounds`. |
| Smooth-solution Galerkin stability and fixed-datum continuum compactness | Explicit `GalerkinAnalyticLaws.smooth_stability` and `.compactness`. |
| Strong continuity, generator-domain equality, and selfadjoint Hamiltonian realization | Not supplied by raw `hamiltonianExpression`, the compact-smooth test predicate, or the conditional L2 isometric equivalence. |
| Literal identification with TXT pressure mean-zero gauge | Separate gauge adapter remains required; exact native `FeffermanB` is unchanged and arbitrary mean is retained. |
| Original 75 checkpoint cards / 361 prospective declarations | This selected index does not resolve or promote any complete original card. The checkpoint manifest remains authoritative. |

`SOURCE_VERIFIED ≠ A_TIER`. `A_TIER_CANDIDATE + conditional premises ≠ UNCONDITIONAL_CLOSURE`. Only a matching external cached run and theorem-level axiom audit may promote the exact native theorem with its displayed premises.
