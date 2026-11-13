import SingularClosure.FourierSeriesCalculus
import SingularClosure.LatticeSobolevSummability

/-! All-order Fourier Sobolev membership yields a literal smooth physical Fourier sum. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem sobolevWeightedCoeff_norm_eq (s : ℕ) (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s c ki‖ = torusSobolevWeight ki.1 ^ s * ‖c ki.1 ki.2‖ := by
  simp only [sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos ki.1)]

theorem sobolev_component_square_summable (s : ℕ) (c : FourierCoeff)
    (hc : Memℓp (sobolevWeightedCoeff s c) 2) (i : Fin 3) :
    Summable (fun k : Frequency => ‖sobolevWeightedCoeff s c (k, i)‖ ^ 2) := by
  have hs : Summable (fun ki : FourierIndex => ‖sobolevWeightedCoeff s c ki‖ ^ 2) := by
    have h := hc.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  exact hs.comp_injective (fun k l h => congrArg Prod.fst h)

/-- Two additional actual Sobolev orders imply absolute coefficient moment summability. -/
theorem sobolev_weighted_component_summable (m : ℕ) (c : FourierCoeff)
    (hc : Memℓp (sobolevWeightedCoeff (m + 2) c) 2) (i : Fin 3) :
    Summable (fun k : Frequency => torusSobolevWeight k ^ m * ‖c k i‖) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _) (norm_nonneg _)) _
    ((sobolev_component_square_summable (m + 2) c hc i).add
      summable_torusSobolevWeight_inv_four)
  intro k
  have hproduct : torusSobolevWeight k ^ m * ‖c k i‖ =
      ‖sobolevWeightedCoeff (m + 2) c (k, i)‖ * (torusSobolevWeight k)⁻¹ ^ 2 := by
    rw [sobolevWeightedCoeff_norm_eq, pow_add]
    field_simp [(torusSobolevWeight_pos k).ne'] <;> ring
  rw [hproduct]
  have hs := sq_nonneg
    (‖sobolevWeightedCoeff (m + 2) c (k, i)‖ - (torusSobolevWeight k)⁻¹ ^ 2)
  have hA := sq_nonneg ‖sobolevWeightedCoeff (m + 2) c (k, i)‖
  have hB := sq_nonneg ((torusSobolevWeight k)⁻¹ ^ 2)
  have hpow : ((torusSobolevWeight k)⁻¹ ^ 2) ^ 2 = (torusSobolevWeight k)⁻¹ ^ 4 := by ring
  nlinarith only [hs, hA, hB, hpow]

def fourierPhaseWeightConstant : ℝ :=
  (2 * Real.pi) * ∑ j : Fin 3,
    ‖Complex.ofRealCLM.comp (EuclideanSpace.proj j : Vec →L[ℝ] ℝ)‖

theorem fourierPhaseWeightConstant_nonneg : 0 ≤ fourierPhaseWeightConstant :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => norm_nonneg _))

theorem fourierPhaseCLM_norm_le_weight (k : Frequency) :
    ‖fourierPhaseCLM k‖ ≤ fourierPhaseWeightConstant * torusSobolevWeight k := by
  have hcoord (j : Fin 3) : |(k j : ℝ)| ≤ torusSobolevWeight k := by
    have h := (norm_le_pi_norm (fun l : Fin 3 => (k l : ℝ)) j).trans
      (frequencyLatticePoint_norm_le_weight k)
    simpa only [Real.norm_eq_abs] using h
  unfold fourierPhaseCLM
  calc
    _ ≤ ∑ j : Fin 3, ‖derivativeSymbol j k •
        (Complex.ofRealCLM.comp (EuclideanSpace.proj j : Vec →L[ℝ] ℝ))‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) *
        ‖Complex.ofRealCLM.comp (EuclideanSpace.proj j : Vec →L[ℝ] ℝ)‖ := by
      simp only [norm_smul, derivativeSymbol_norm]
    _ ≤ ∑ j : Fin 3, ((2 * Real.pi) * torusSobolevWeight k) *
        ‖Complex.ofRealCLM.comp (EuclideanSpace.proj j : Vec →L[ℝ] ℝ)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcoord j) (by positivity)) (norm_nonneg _)
    _ = fourierPhaseWeightConstant * torusSobolevWeight k := by
      rw [← Finset.mul_sum]
      unfold fourierPhaseWeightConstant
      ring

theorem ALL_SOBOLEV_IMP_RAPID_SCALAR (c : FourierCoeff)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c) 2) (i : Fin 3) :
    RapidScalarFourier (fun k => c k i) := by
  intro m
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) _
    ((sobolev_weighted_component_summable m c (hc (m + 2)) i).mul_left
      (fourierPhaseWeightConstant ^ m))
  intro k
  calc
    _ ≤ ‖c k i‖ * (fourierPhaseWeightConstant * torusSobolevWeight k) ^ m :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (fourierPhaseCLM_norm_le_weight k) m) (norm_nonneg _)
    _ = _ := by rw [mul_pow]; ring

def smoothFourierSynthesis (c : FourierCoeff) : Field :=
  fun x => WithLp.toLp 2 (fun i : Fin 3 => (scalarFourierSeries (fun k => c k i) x).re)

theorem smoothFourierSynthesis_contDiff (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i)) :
    ContDiff ℝ ∞ (smoothFourierSynthesis c) := by
  apply (contDiff_piLp 2).2
  intro i
  exact realFourierSeries_contDiff (hc i)

theorem smoothFourierSynthesis_periodic (c : FourierCoeff) :
    SpatialPeriodic (smoothFourierSynthesis c) := by
  intro x j
  ext i
  exact realFourierSeries_periodic (fun k => c k i) x j

theorem smoothFourierSynthesis_coordinateDerivative (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i)) (j : Fin 3) :
    coordinateDerivative (smoothFourierSynthesis c) j =
      smoothFourierSynthesis (spectralMultiplier (derivativeSymbol j) c) := by
  funext x
  ext i
  have hd := ((smoothFourierSynthesis_contDiff c hc).differentiable (by simp) x).hasFDerivAt
  have hp := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x hd
  have hr := ((realFourierSeries_contDiff (hc i)).differentiable (by simp) x).hasFDerivAt
  have he := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) (hp.unique hr)
  have hscalar := realFourierSeries_gradient_apply
    (hc i).summable_norm (hc i).summable_first x j
  change fderiv ℝ (realFourierSeries (fun k => c k i)) x (unitVector j) = _ at hscalar
  calc
    coordinateDerivative (smoothFourierSynthesis c) j x i =
        fderiv ℝ (realFourierSeries (fun k => c k i)) x (unitVector j) := by
      simpa only [coordinateDerivative, ContinuousLinearMap.comp_apply,
        EuclideanSpace.coe_proj] using he
    _ = _ := hscalar

theorem smoothFourierSynthesis_meanZero (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i)) (hzero : SpectralMeanZero c) :
    MeanZero (smoothFourierSynthesis c) := by
  have hint : IntegrableOn (smoothFourierSynthesis c) unitCube volume :=
    (smoothFourierSynthesis_contDiff c hc).continuous.continuousOn.integrableOn_compact
      isCompact_unitCube
  refine ⟨hint, ?_⟩
  ext i
  have hproj := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).integral_comp_comm hint
  have he : spatialMean (smoothFourierSynthesis c) i =
      ∫ x in unitCube, smoothFourierSynthesis c x i := by
    simpa only [spatialMean, EuclideanSpace.coe_proj] using hproj.symm
  change spatialMean (smoothFourierSynthesis c) i = 0
  rw [he]
  exact (realFourierSeries_meanZero (hc i).summable_norm (hzero i)).2

theorem smoothFourierSynthesis_divergence_free (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hsol : SpectralSolenoidal c) (x : Vec) :
    divergence (smoothFourierSynthesis c) x = 0 := by
  have hs (i : Fin 3) : Summable (fun k : Frequency =>
      fourierCharacter k x * (derivativeSymbol i k * c k i)) := by
    have h := scalarFourierSeries_summable ((hc i).directional (unitVector i)).summable_norm x
    simpa only [fourierPhaseCLM_unitVector] using h
  unfold divergence
  simp only [smoothFourierSynthesis_coordinateDerivative c hc, smoothFourierSynthesis,
    spectralMultiplier, scalarFourierSeries]
  rw [← physical_complex_re_sum]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  have hterm (k : Frequency) :
      (∑ i : Fin 3, fourierCharacter k x * (derivativeSymbol i k * c k i)) = 0 := by
    calc
      _ = fourierCharacter k x * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
          (∑ i : Fin 3, (k i : ℂ) * c k i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_intCast]
        ring
      _ = 0 := by rw [hsol k]; ring
  simp only [hterm, tsum_zero, Complex.zero_re]

theorem smoothFourierSynthesis_smoothSigmaZero (c : FourierCoeff)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c) 2)
    (hzero : SpectralMeanZero c) (hsol : SpectralSolenoidal c) :
    SmoothSigmaZero (smoothFourierSynthesis c) := by
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR c hc
  exact ⟨smoothFourierSynthesis_contDiff c hr, smoothFourierSynthesis_periodic c,
    smoothFourierSynthesis_divergence_free c hr hsol,
    smoothFourierSynthesis_meanZero c hr hzero⟩

/-- The conjugate-symmetric coefficient array has a genuinely real Fourier sum. -/
theorem scalarFourierSeries_star_eq_self (c : FourierCoeff)
    (hreal : SpectralReality c) (i : Fin 3) (x : Vec) :
    star (scalarFourierSeries (fun k => c k i) x) =
      scalarFourierSeries (fun k => c k i) x := by
  unfold scalarFourierSeries
  rw [tsum_star]
  calc
    _ = ∑' k : Frequency, fourierCharacter (-k) x * c (-k) i := by
      apply tsum_congr
      intro k
      rw [star_mul, fourierCharacter_neg, hreal] <;> ring
    _ = _ := (Equiv.neg Frequency).tsum_eq
      (fun k => fourierCharacter k x * c k i)

theorem scalarFourierSeries_eq_smoothFourierSynthesis_component
    (c : FourierCoeff) (hreal : SpectralReality c) (i : Fin 3) (x : Vec) :
    scalarFourierSeries (fun k => c k i) x =
      (smoothFourierSynthesis c x i : ℂ) := by
  have h := congrArg Complex.im (scalarFourierSeries_star_eq_self c hreal i x)
  apply Complex.ext
  · rfl
  · change (scalarFourierSeries (fun k => c k i) x).im = 0
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith

/-- Fourier coefficient recovery follows from absolute convergence and actual cube integration. -/
theorem scalarFourierSeries_coefficient {b : Frequency → ℂ}
    (hb : Summable (fun k => ‖b k‖)) (k : Frequency) :
    (∫ x in unitCube, star (fourierCharacter k x) * scalarFourierSeries b x) = b k := by
  classical
  have hint (l : Frequency) : IntegrableOn
      (fun x : Vec => star (fourierCharacter k x) * (fourierCharacter l x * b l))
      unitCube volume :=
    ((fourierCharacter_contDiff k).continuous.star.mul
      ((fourierCharacter_contDiff l).continuous.mul continuous_const)).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hnorm : Summable (fun l : Frequency =>
      ∫ x in unitCube, ‖star (fourierCharacter k x) * (fourierCharacter l x * b l)‖) := by
    simpa only [norm_mul, norm_star, fourierCharacter_norm, one_mul,
      setIntegral_const, smul_eq_mul] using hb.mul_left (volume.real unitCube)
  calc
    _ = ∫ x in unitCube, ∑' l : Frequency,
        star (fourierCharacter k x) * (fourierCharacter l x * b l) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact (tsum_mul_left :
        (∑' l : Frequency, star (fourierCharacter k x) * (fourierCharacter l x * b l)) =
          star (fourierCharacter k x) * ∑' l : Frequency, fourierCharacter l x * b l).symm
    _ = ∑' l : Frequency, ∫ x in unitCube,
        star (fourierCharacter k x) * (fourierCharacter l x * b l) :=
      (integral_tsum_of_summable_integral_norm hint hnorm).symm
    _ = ∑' l : Frequency, if l = k then b k else 0 := by
      apply tsum_congr
      intro l
      have h := integral_complex_character_pair k l 1 (b l)
      by_cases hl : l = k
      · subst l
        simpa using h
      · simpa [hl, Ne.symm hl] using h
    _ = b k := by simp

theorem datumFourierCoeff_smoothFourierSynthesis (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) :
    datumFourierCoeff (smoothFourierSynthesis c) = c := by
  funext k i
  unfold datumFourierCoeff datumFourierIntegrand
  simp_rw [← scalarFourierSeries_eq_smoothFourierSynthesis_component c hreal]
  exact scalarFourierSeries_coefficient (hc i).summable_norm k

/-- The actual smooth physical realization has exactly the original coefficients. -/
theorem ALL_SOBOLEV_SMOOTH_PHYSICAL_REALIZATION (c : FourierCoeff)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c) 2)
    (hreal : SpectralReality c) (hzero : SpectralMeanZero c)
    (hsol : SpectralSolenoidal c) :
    SmoothSigmaZero (smoothFourierSynthesis c) ∧
      datumFourierCoeff (smoothFourierSynthesis c) = c :=
  ⟨smoothFourierSynthesis_smoothSigmaZero c hc hzero hsol,
    datumFourierCoeff_smoothFourierSynthesis c (ALL_SOBOLEV_IMP_RAPID_SCALAR c hc) hreal⟩

end

end SingularClosure
