import SingularClosure.FourierTransport
import SingularClosure.SobolevSmoothRealization
import SingularClosure.SmoothDatumSobolev

/-!
# Actual physical product coefficients of the smooth Fourier realization

Absolute coefficient convergence justifies exchanging the Fourier series with
the literal cube integral. Periodic integration by parts then identifies the
actual convection coefficients with the untruncated divergence convolution.
No Fourier-product or nonlinear-equation agreement is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Product coefficients derived from genuine convergent scalar Fourier sums. -/
theorem scalarFourierSeries_product_coefficient
    (b d : Frequency → ℂ) (hb : Summable (fun p => ‖b p‖))
    (hd : Summable (fun p => ‖d p‖)) (k : Frequency) :
    (∫ x in unitCube, star (fourierCharacter k x) *
      (scalarFourierSeries b x * scalarFourierSeries d x)) =
        ∑' p : Frequency, b p * d (k - p) := by
  have hcont := scalarFourierSeries_continuous hd
  have hint (p : Frequency) : IntegrableOn (fun x : Vec =>
      star (fourierCharacter k x) *
        ((fourierCharacter p x * b p) * scalarFourierSeries d x)) unitCube volume :=
    ((fourierCharacter_contDiff k).continuous.star.mul
      (((fourierCharacter_contDiff p).continuous.mul continuous_const).mul hcont)).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hnorm : Summable (fun p : Frequency => ∫ x in unitCube,
      ‖star (fourierCharacter k x) *
        ((fourierCharacter p x * b p) * scalarFourierSeries d x)‖) := by
    simp only [norm_mul, norm_star, fourierCharacter_norm, one_mul]
    simp_rw [integral_const_mul]
    exact hb.mul_right (∫ x in unitCube, ‖scalarFourierSeries d x‖)
  calc
    _ = ∫ x in unitCube, ∑' p : Frequency,
        star (fourierCharacter k x) *
          ((fourierCharacter p x * b p) * scalarFourierSeries d x) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change star (fourierCharacter k x) *
        ((∑' p : Frequency, fourierCharacter p x * b p) * scalarFourierSeries d x) = _
      rw [← tsum_mul_right, ← tsum_mul_left]
    _ = ∑' p : Frequency, ∫ x in unitCube,
        star (fourierCharacter k x) *
          ((fourierCharacter p x * b p) * scalarFourierSeries d x) :=
      (integral_tsum_of_summable_integral_norm hint hnorm).symm
    _ = _ := by
      apply tsum_congr
      intro p
      have hchar (x : Vec) : star (fourierCharacter k x) * fourierCharacter p x =
          star (fourierCharacter (k - p) x) := by
        rw [← fourierCharacter_neg, fourierCharacter_mul, ← fourierCharacter_neg]
        congr 1
        abel
      calc
        _ = ∫ x in unitCube, b p *
            (star (fourierCharacter (k - p) x) * scalarFourierSeries d x) := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro x
          change star (fourierCharacter k x) *
            (fourierCharacter p x * b p * scalarFourierSeries d x) =
              b p * (star (fourierCharacter (k - p) x) * scalarFourierSeries d x)
          rw [← hchar x]
          ring
        _ = b p * (∫ x in unitCube,
            star (fourierCharacter (k - p) x) * scalarFourierSeries d x) :=
          integral_const_mul _ _
        _ = _ := by rw [scalarFourierSeries_coefficient hd]

/-- A concrete rank-one physical tensor column. -/
def physicalTensorColumn (u v : Field) (j : Fin 3) : Field :=
  fun x => u x j • v x

theorem physicalTensorColumn_contDiff (u v : Field)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (j : Fin 3) :
    ContDiff ℝ ∞ (physicalTensorColumn u v j) :=
  ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).contDiff.comp hu).smul hv

theorem physicalTensorColumn_periodic (u v : Field)
    (hu : SpatialPeriodic u) (hv : SpatialPeriodic v) (j : Fin 3) :
    SpatialPeriodic (physicalTensorColumn u v j) := by
  intro x l
  simp only [physicalTensorColumn, hu x l, hv x l]

theorem physicalTensorColumn_coordinateDerivative (u v : Field)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (j l : Fin 3) (x : Vec) :
    coordinateDerivative (physicalTensorColumn u v j) l x =
      u x j • coordinateDerivative v l x + coordinateDerivative u l x j • v x := by
  have hp := (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).hasFDerivAt.comp x (hu x).hasFDerivAt
  have hs := hp.smul (hv x).hasFDerivAt
  have hs' : HasFDerivAt (physicalTensorColumn u v j)
      (u x j • fderiv ℝ v x +
        ((EuclideanSpace.proj j).comp (fderiv ℝ u x)).smulRight (v x)) x := by
    simpa only [physicalTensorColumn, Function.comp_def, Pi.smul_def',
      EuclideanSpace.coe_proj] using! hs
  change fderiv ℝ (physicalTensorColumn u v j) x (unitVector l) = _
  rw [hs'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    EuclideanSpace.coe_proj, coordinateDerivative]

/-- Solenoidal convection is the literal divergence of the physical tensor. -/
theorem convection_eq_tensor_divergence (u : Field)
    (hu : Differentiable ℝ u) (hdiv : ∀ x : Vec, divergence u x = 0) (x : Vec) :
    convection u x = ∑ j : Fin 3,
      coordinateDerivative (physicalTensorColumn u u j) j x := by
  simp_rw [physicalTensorColumn_coordinateDerivative u u hu hu]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul]
  change convection u x = (∑ j : Fin 3, u x j • coordinateDerivative u j x) +
    divergence u x • u x
  rw [hdiv, zero_smul, add_zero]
  exact convection_eq_sum_coordinateDerivative u x

theorem datumFourierCoeff_physicalTensorColumn
    (c : FourierCoeff) (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) (j : Fin 3) (k : Frequency) (i : Fin 3) :
    datumFourierCoeff (physicalTensorColumn
      (smoothFourierSynthesis c) (smoothFourierSynthesis c) j) k i =
        ∑' p : Frequency, c p j * c (k - p) i := by
  change (∫ x in unitCube, star (fourierCharacter k x) *
    ((smoothFourierSynthesis c x j * smoothFourierSynthesis c x i : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_mul]
  simp_rw [← scalarFourierSeries_eq_smoothFourierSynthesis_component c hreal]
  exact scalarFourierSeries_product_coefficient _ _
    (hc j).summable_norm (hc i).summable_norm k

def fullTransportCoefficients (c : TorusSobolev 0) : FourierCoeff :=
  fun k i => divergenceTransportCoefficient k i c c

/-- Actual physical convection has the untruncated divergence-form Fourier coefficients. -/
theorem smoothFourierSynthesis_convection_coeff (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    datumFourierCoeff (convection (smoothFourierSynthesis c.val)) =
      fullTransportCoefficients c := by
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR c.val hc
  let u : Field := smoothFourierSynthesis c.val
  have hu : ContDiff ℝ ∞ u := smoothFourierSynthesis_contDiff c.val hr
  have hp : SpatialPeriodic u := smoothFourierSynthesis_periodic c.val
  have hdiv : ∀ x : Vec, divergence u x = 0 :=
    smoothFourierSynthesis_divergence_free c.val hr hsol
  have hcol (j : Fin 3) : ContDiff ℝ ∞ (physicalTensorColumn u u j) :=
    physicalTensorColumn_contDiff u u hu hu j
  have hpcol (j : Fin 3) : SpatialPeriodic (physicalTensorColumn u u j) :=
    physicalTensorColumn_periodic u u hp hp j
  have hdercont (j : Fin 3) : Continuous
      (coordinateDerivative (physicalTensorColumn u u j) j) :=
    coordinateDerivative_continuous (hcol j) j
  funext k i
  have hid (x : Vec) : datumFourierIntegrand (convection u) k i x =
      ∑ j : Fin 3,
        datumFourierIntegrand (coordinateDerivative (physicalTensorColumn u u j) j) k i x := by
    have h := congrArg (EuclideanSpace.proj i : Vec →L[ℝ] ℝ)
      (convection_eq_tensor_divergence u (hu.differentiable (by simp)) hdiv x)
    have hi : convection u x i = ∑ j : Fin 3,
        coordinateDerivative (physicalTensorColumn u u j) j x i := by
      simpa only [map_sum, EuclideanSpace.coe_proj] using h
    simp only [datumFourierIntegrand, hi, Complex.ofReal_sum, Finset.mul_sum]
  change (∫ x in unitCube, datumFourierIntegrand (convection u) k i x) = _
  simp_rw [hid]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => datumFourierIntegrand
      (coordinateDerivative (physicalTensorColumn u u j) j) k i x)
    (fun j _ => datumFourierIntegrand_integrableOn
      (hdercont j) k i)]
  change (∑ j : Fin 3,
    datumFourierCoeff (coordinateDerivative (physicalTensorColumn u u j) j) k i) = _
  have hD (j : Fin 3) :
      datumFourierCoeff (coordinateDerivative (physicalTensorColumn u u j) j) k i =
        derivativeSymbol j k * datumFourierCoeff (physicalTensorColumn u u j) k i := by
    have h := congrArg (fun a : FourierCoeff => a k i)
      (datumFourierCoeff_coordinateDerivative j (physicalTensorColumn u u j) (hcol j) (hpcol j))
    simpa only [spectralMultiplier] using h
  simp_rw [hD]
  change (∑ j : Fin 3, derivativeSymbol j k *
    datumFourierCoeff (physicalTensorColumn (smoothFourierSynthesis c.val)
      (smoothFourierSynthesis c.val) j) k i) = divergenceTransportCoefficient k i c c
  simp_rw [datumFourierCoeff_physicalTensorColumn c.val hr hreal]
  exact (divergenceTransportCoefficient_apply k i c c).symm

theorem convection_contDiff (u : Field) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (convection u) :=
  (contDiff_infty_iff_fderiv.mp hu).2.clm_apply hu

theorem convection_periodic (u : Field) (hu : SpatialPeriodic u) :
    SpatialPeriodic (convection u) := by
  intro x i
  rw [convection_eq_sum_coordinateDerivative, convection_eq_sum_coordinateDerivative]
  apply Finset.sum_congr rfl
  intro j _
  rw [hu x i, coordinateDerivative_spatialPeriodic j u hu x i]

theorem divergenceTransport_allSobolev (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) (s : ℕ) :
    Memℓp (sobolevWeightedCoeff s (fullTransportCoefficients c)) 2 := by
  rw [← smoothFourierSynthesis_convection_coeff c hc hreal hsol]
  exact SMOOTH_DATUM_MEM_TORUS_SOBOLEV s _
    (convection_contDiff _ (smoothFourierSynthesis_contDiff c.val
      (ALL_SOBOLEV_IMP_RAPID_SCALAR c.val hc)))
    (convection_periodic _ (smoothFourierSynthesis_periodic c.val))

theorem divergenceTransport_rapid (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) (i : Fin 3) :
    RapidScalarFourier (fun k => fullTransportCoefficients c k i) :=
  ALL_SOBOLEV_IMP_RAPID_SCALAR _ (divergenceTransport_allSobolev c hc hreal hsol) i

theorem divergenceTransport_reality (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    SpectralReality (fullTransportCoefficients c) := by
  rw [← smoothFourierSynthesis_convection_coeff c hc hreal hsol]
  exact datumFourierCoeff_reality _

end

end SingularClosure
