import SingularClosure.SobolevSmoothRealization
import SingularClosure.PeriodicPoincare
import SingularClosure.FourierProduct

/-! Actual infinite Fourier pressure. The scalar multiplier is the same as the
finite pressure multiplier, including its sign. Rapid summability is preserved
by a proved bound on that multiplier. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem frequency_coord_abs_le_freqSq (k : Frequency) (i : Fin 3) :
    |(k i : ℝ)| ≤ (galerkinFreqSq k : ℝ) := by
  have hcoord : |k i| ≤ (k i) ^ 2 := by
    by_cases hz : k i = 0
    · simp [hz]
    · by_cases hp : 0 ≤ k i
      · have hpos : 1 ≤ k i := by omega
        rw [abs_of_nonneg hp]
        nlinarith
      · have hneg : k i ≤ -1 := by omega
        rw [abs_of_neg (lt_of_not_ge hp)]
        nlinarith
  have hsum : (k i) ^ 2 ≤ galerkinFreqSq k :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 3 => (k j) ^ 2)
      (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i)
  exact_mod_cast hcoord.trans hsum

/-- The pressure multiplier is uniformly bounded on every nonzero integer
frequency; the zero frequency is fixed to zero by definition. -/
theorem pressureFromTransport_norm_le (k : Frequency) (b : Fin 3 → ℂ) :
    ‖pressureFromTransport k b‖ ≤ ∑ i : Fin 3, ‖b i‖ := by
  by_cases hk : k = 0
  · subst k
    have hzero : pressureFromTransport (0 : Frequency) b = 0 := by
      rw [pressureFromTransport, if_pos rfl]
    rw [hzero, norm_zero]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
  have hfreq : (1 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_ge_one_of_ne_zero k hk
  have hsum : (∑ i : Fin 3, (k i : ℂ) ^ 2) = ((galerkinFreqSq k : ℝ) : ℂ) := by
    simp [galerkinFreqSq]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi1 : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hden : 0 < (2 * Real.pi) * (galerkinFreqSq k : ℝ) :=
    mul_pos hpi (lt_of_lt_of_le zero_lt_one hfreq)
  have hnum : ‖∑ i : Fin 3, (k i : ℂ) * b i‖ ≤
      (galerkinFreqSq k : ℝ) * ∑ i : Fin 3, ‖b i‖ := by
    calc
      _ ≤ ∑ i : Fin 3, ‖(k i : ℂ) * b i‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, |(k i : ℝ)| * ‖b i‖ := by
        simp only [norm_mul, Complex.norm_intCast, Int.cast_abs]
      _ ≤ ∑ i : Fin 3, (galerkinFreqSq k : ℝ) * ‖b i‖ :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (frequency_coord_abs_le_freqSq k i) (norm_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  simp only [pressureFromTransport, hk, if_false, norm_div, norm_mul,
    Complex.norm_I, one_mul, hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpi, abs_of_pos Real.pi_pos,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (zero_le_one.trans hfreq)]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ (galerkinFreqSq k : ℝ) * ∑ i : Fin 3, ‖b i‖ := hnum
    _ ≤ ((2 * Real.pi) * (galerkinFreqSq k : ℝ)) * ∑ i : Fin 3, ‖b i‖ :=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (zero_le_one.trans hfreq) hpi1)
        (Finset.sum_nonneg (fun i _ => norm_nonneg (b i)))
    _ = _ := mul_comm _ _

def infinitePressureCoefficient (b : FourierCoeff) (k : Frequency) : ℂ :=
  pressureFromTransport k (b k)

@[simp]
theorem infinitePressureCoefficient_zero (b : FourierCoeff) :
    infinitePressureCoefficient b 0 = 0 := by
  simp [infinitePressureCoefficient, pressureFromTransport]

theorem infinitePressureCoefficient_rapid (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i)) :
    RapidScalarFourier (infinitePressureCoefficient b) := by
  intro m
  have hs : Summable (fun k : Frequency =>
      ∑ i : Fin 3, ‖b k i‖ * ‖fourierPhaseCLM k‖ ^ m) :=
    summable_sum (fun i _ => hb i m)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) _ hs
  intro k
  calc
    _ ≤ (∑ i : Fin 3, ‖b k i‖) * ‖fourierPhaseCLM k‖ ^ m :=
      mul_le_mul_of_nonneg_right (pressureFromTransport_norm_le k (b k))
        (pow_nonneg (norm_nonneg _) _)
    _ = _ := Finset.sum_mul ..

theorem infinitePressureCoefficient_reality (b : FourierCoeff) (hb : SpectralReality b)
    (k : Frequency) :
    infinitePressureCoefficient b (-k) = star (infinitePressureCoefficient b k) := by
  have he : b (-k) = fun i => star (b k i) := funext (fun i => hb k i)
  simp only [infinitePressureCoefficient, he, pressureFromTransport_neg_star]

/-- The literal real Fourier series defining the infinite pressure. -/
def infiniteTransportPressure (b : FourierCoeff) : Vec → ℝ :=
  realFourierSeries (infinitePressureCoefficient b)

theorem infiniteTransportPressure_contDiff (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i)) :
    ContDiff ℝ ∞ (infiniteTransportPressure b) :=
  realFourierSeries_contDiff (infinitePressureCoefficient_rapid b hb)

theorem infiniteTransportPressure_periodic (b : FourierCoeff) :
    SpatialPeriodic (infiniteTransportPressure b) :=
  realFourierSeries_periodic _

theorem infiniteTransportPressure_meanZero (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i)) :
    PressureMeanZero (infiniteTransportPressure b) :=
  realFourierSeries_meanZero
    (infinitePressureCoefficient_rapid b hb).summable_norm
    (infinitePressureCoefficient_zero b)

theorem pressure_derivativeSymbol_recovery (k : Frequency) (b : Fin 3 → ℂ) (i : Fin 3) :
    derivativeSymbol i k * pressureFromTransport k b = coefficientLeray k b i - b i := by
  have h := pressureFromTransport_recovery k b i
  have hs : derivativeSymbol i k =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k i : ℂ) := by
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  rw [hs]
  linear_combination h

/-- The actual pressure gradient has the longitudinal Fourier correction with
the sign required by b + grad p = Leray b. -/
theorem infiniteTransportPressure_gradient (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i)) :
    gradient (infiniteTransportPressure b) =
      smoothFourierSynthesis (fun k i => coefficientLeray k (b k) i - b k i) := by
  have hp := infinitePressureCoefficient_rapid b hb
  funext x
  ext i
  have h := realFourierSeries_gradient_apply hp.summable_norm hp.summable_first x i
  change gradient (realFourierSeries (infinitePressureCoefficient b)) x i = _
  rw [h]
  change (∑' k : Frequency, fourierCharacter k x *
      (derivativeSymbol i k * infinitePressureCoefficient b k)).re = _
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  rw [infinitePressureCoefficient, pressure_derivativeSymbol_recovery]

/-- Pointwise physical recovery for the genuinely convergent infinite series. -/
theorem infiniteTransportPressure_recovery (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i)) (x : Vec) :
    smoothFourierSynthesis b x + gradient (infiniteTransportPressure b) x =
      smoothFourierSynthesis (fun k => coefficientLeray k (b k)) x := by
  have hp := infinitePressureCoefficient_rapid b hb
  ext i
  have hgrad := realFourierSeries_gradient_apply hp.summable_norm hp.summable_first x i
  have hfirst : Summable (fun k : Frequency => fourierCharacter k x * b k i) :=
    scalarFourierSeries_summable (hb i).summable_norm x
  have hsecond : Summable (fun k : Frequency => fourierCharacter k x *
      (derivativeSymbol i k * infinitePressureCoefficient b k)) := by
    have h := scalarFourierSeries_summable (hp.directional (unitVector i)).summable_norm x
    simpa only [fourierPhaseCLM_unitVector] using h
  change (scalarFourierSeries (fun k => b k i) x).re +
    gradient (realFourierSeries (infinitePressureCoefficient b)) x i = _
  rw [hgrad, ← Complex.add_re]
  unfold scalarFourierSeries
  rw [← hfirst.tsum_add hsecond]
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  rw [infinitePressureCoefficient, pressure_derivativeSymbol_recovery]
  ring

theorem infinitePressureGradient_rapid (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i)) (i : Fin 3) :
    RapidScalarFourier (fun k => coefficientLeray k (b k) i - b k i) := by
  have h := (infinitePressureCoefficient_rapid b hb).directional (unitVector i)
  simpa only [fourierPhaseCLM_unitVector, infinitePressureCoefficient,
    pressure_derivativeSymbol_recovery] using h

theorem infinitePressureGradient_reality (b : FourierCoeff) (hb : SpectralReality b) :
    SpectralReality (fun k i => coefficientLeray k (b k) i - b k i) := by
  intro k i
  have he : b (-k) = fun j => star (b k j) := funext (fun j => hb k j)
  simp only [he, coefficientLeray_neg_star, star_sub]

/-- Recovery concerns the literal cube Fourier integrals of the literal
physical pressure gradient. -/
theorem infiniteTransportPressure_gradient_coeff (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i))
    (hreal : SpectralReality b) :
    datumFourierCoeff (gradient (infiniteTransportPressure b)) =
      fun k i => coefficientLeray k (b k) i - b k i := by
  rw [infiniteTransportPressure_gradient b hb]
  exact datumFourierCoeff_smoothFourierSynthesis _
    (infinitePressureGradient_rapid b hb) (infinitePressureGradient_reality b hreal)

theorem infiniteTransportPressure_complex_series (b : FourierCoeff)
    (hreal : SpectralReality b) (x : Vec) :
    (infiniteTransportPressure b x : ℂ) =
      scalarFourierSeries (infinitePressureCoefficient b) x := by
  let q : FourierCoeff := fun k _ => infinitePressureCoefficient b k
  have hq : SpectralReality q := fun k _ => infinitePressureCoefficient_reality b hreal k
  exact (scalarFourierSeries_eq_smoothFourierSynthesis_component q hq 0 x).symm

theorem infiniteTransportPressure_coeff (b : FourierCoeff)
    (hb : ∀ i : Fin 3, RapidScalarFourier (fun k => b k i))
    (hreal : SpectralReality b) (k : Frequency) :
    (∫ x in unitCube, star (fourierCharacter k x) * (infiniteTransportPressure b x : ℂ)) =
      infinitePressureCoefficient b k := by
  simp_rw [infiniteTransportPressure_complex_series b hreal]
  exact scalarFourierSeries_coefficient
    (infinitePressureCoefficient_rapid b hb).summable_norm k

/-- Pressure of the actual untruncated transport of the actual Sobolev state. -/
def fullTransportPressure (c : TorusSobolev 0) : Vec → ℝ :=
  infiniteTransportPressure (fullTransportCoefficients c)

theorem fullTransportPressure_coefficient_rapid (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    RapidScalarFourier (infinitePressureCoefficient (fullTransportCoefficients c)) :=
  infinitePressureCoefficient_rapid _ (divergenceTransport_rapid c hc hreal hsol)

theorem fullTransportPressure_coefficient_reality (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) (k : Frequency) :
    infinitePressureCoefficient (fullTransportCoefficients c) (-k) =
      star (infinitePressureCoefficient (fullTransportCoefficients c) k) :=
  infinitePressureCoefficient_reality _ (divergenceTransport_reality c hc hreal hsol) k

theorem fullTransportPressure_contDiff (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    ContDiff ℝ ∞ (fullTransportPressure c) :=
  infiniteTransportPressure_contDiff _ (divergenceTransport_rapid c hc hreal hsol)

theorem fullTransportPressure_periodic (c : TorusSobolev 0) :
    SpatialPeriodic (fullTransportPressure c) :=
  infiniteTransportPressure_periodic _

theorem fullTransportPressure_meanZero (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    PressureMeanZero (fullTransportPressure c) :=
  infiniteTransportPressure_meanZero _ (divergenceTransport_rapid c hc hreal hsol)

theorem fullTransportPressure_gradient_coeff (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    datumFourierCoeff (gradient (fullTransportPressure c)) =
      fun k i => coefficientLeray k (fullTransportCoefficients c k) i -
        fullTransportCoefficients c k i :=
  infiniteTransportPressure_gradient_coeff _
    (divergenceTransport_rapid c hc hreal hsol) (divergenceTransport_reality c hc hreal hsol)

/-- Infinite pressure recovery for actual transport coefficients. All analytic
summability premises are discharged from the stated Sobolev membership of c. -/
theorem INFINITE_TRANSPORT_PRESSURE_RECOVERY (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    ContDiff ℝ ∞ (fullTransportPressure c) ∧
      SpatialPeriodic (fullTransportPressure c) ∧
      PressureMeanZero (fullTransportPressure c) ∧
      ∀ x : Vec, smoothFourierSynthesis (fullTransportCoefficients c) x +
        gradient (fullTransportPressure c) x =
        smoothFourierSynthesis
          (fun k => coefficientLeray k (fullTransportCoefficients c k)) x := by
  refine ⟨fullTransportPressure_contDiff c hc hreal hsol,
    fullTransportPressure_periodic c, fullTransportPressure_meanZero c hc hreal hsol, ?_⟩
  exact infiniteTransportPressure_recovery _ (divergenceTransport_rapid c hc hreal hsol)

end

end SingularClosure
