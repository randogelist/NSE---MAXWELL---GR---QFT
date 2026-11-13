import SingularClosure.FourierPressure
import SingularClosure.FourierDecay
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Calculus of genuinely convergent scalar Fourier series

The decay predicate consists only of explicit weighted summability conditions
on the scalar coefficients. Its weight is the operator norm of the concrete
Fourier phase from `PhysicalProjection`. Termwise differentiation, all finite
orders of smoothness, periodicity, and the physical spatial mean are derived.
No pressure recovery, nonlinear smoothing, or Fourier convergence conclusion
is included among the premises.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Explicit polynomial moment summability for the actual Fourier phase. -/
def RapidScalarFourier (b : Frequency → ℂ) : Prop :=
  ∀ m : ℕ, Summable (fun k => ‖b k‖ * ‖fourierPhaseCLM k‖ ^ m)

def scalarFourierSeries (b : Frequency → ℂ) (x : Vec) : ℂ :=
  ∑' k : Frequency, fourierCharacter k x * b k

def realFourierSeries (b : Frequency → ℂ) (x : Vec) : ℝ :=
  (scalarFourierSeries b x).re

theorem RapidScalarFourier.summable_norm {b : Frequency → ℂ}
    (hb : RapidScalarFourier b) : Summable (fun k => ‖b k‖) := by
  simpa only [pow_zero, mul_one] using hb 0

theorem RapidScalarFourier.summable_first {b : Frequency → ℂ}
    (hb : RapidScalarFourier b) :
    Summable (fun k => ‖b k‖ * ‖fourierPhaseCLM k‖) := by
  simpa only [pow_one] using hb 1

theorem scalarFourierSeries_summable {b : Frequency → ℂ}
    (hb : Summable (fun k => ‖b k‖)) (x : Vec) :
    Summable (fun k => fourierCharacter k x * b k) := by
  apply Summable.of_norm_bounded hb
  intro k
  simp only [norm_mul, fourierCharacter_norm, one_mul, le_refl]

theorem scalarFourierSeries_continuous {b : Frequency → ℂ}
    (hb : Summable (fun k => ‖b k‖)) : Continuous (scalarFourierSeries b) := by
  exact continuous_tsum
    (fun k => (fourierCharacter_contDiff k).continuous.mul continuous_const) hb
    (fun k x => by simp only [norm_mul, fourierCharacter_norm, one_mul, le_refl])

theorem scalarFourierSeries_periodic (b : Frequency → ℂ) :
    SpatialPeriodic (scalarFourierSeries b) := by
  intro x j
  unfold scalarFourierSeries
  apply tsum_congr
  intro k
  rw [fourierCharacter_periodic k x j]

private theorem scalarFourierDerivative_norm (b : Frequency → ℂ)
    (k : Frequency) (x : Vec) :
    ‖b k • (fourierCharacter k x • fourierPhaseCLM k)‖ =
      ‖b k‖ * ‖fourierPhaseCLM k‖ := by
  simp only [norm_smul, fourierCharacter_norm, one_mul]

theorem scalarFourierDerivative_summable {b : Frequency → ℂ}
    (hb : Summable (fun k => ‖b k‖ * ‖fourierPhaseCLM k‖)) (x : Vec) :
    Summable (fun k => b k • (fourierCharacter k x • fourierPhaseCLM k)) := by
  apply Summable.of_norm_bounded hb
  intro k
  exact (scalarFourierDerivative_norm b k x).le

/-- Actual Fréchet derivative of the convergent series. -/
theorem scalarFourierSeries_hasFDerivAt {b : Frequency → ℂ}
    (hzero : Summable (fun k => ‖b k‖))
    (hone : Summable (fun k => ‖b k‖ * ‖fourierPhaseCLM k‖)) (x : Vec) :
    HasFDerivAt (scalarFourierSeries b)
      (∑' k : Frequency, b k • (fourierCharacter k x • fourierPhaseCLM k)) x := by
  exact hasFDerivAt_tsum hone
    (fun k y => (fourierCharacter_hasFDerivAt k y).mul_const (b k))
    (fun k y => (scalarFourierDerivative_norm b k y).le)
    (scalarFourierSeries_summable hzero (0 : Vec)) x

/-- Every directional derivative is a convergent Fourier multiplier series. -/
theorem scalarFourierSeries_fderiv_apply {b : Frequency → ℂ}
    (hzero : Summable (fun k => ‖b k‖))
    (hone : Summable (fun k => ‖b k‖ * ‖fourierPhaseCLM k‖)) (x y : Vec) :
    fderiv ℝ (scalarFourierSeries b) x y =
      scalarFourierSeries (fun k => fourierPhaseCLM k y * b k) x := by
  rw [(scalarFourierSeries_hasFDerivAt hzero hone x).fderiv]
  have happ := (ContinuousLinearMap.apply ℝ ℂ y).map_tsum
    (scalarFourierDerivative_summable hone x)
  change (∑' k : Frequency, b k • (fourierCharacter k x • fourierPhaseCLM k)) y = _
  calc
    _ = ∑' k : Frequency,
        (b k • (fourierCharacter k x • fourierPhaseCLM k)) y := happ
    _ = _ := by
      apply tsum_congr
      intro k
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring

/-- The concrete weighted decay class is closed under each directional multiplier. -/
theorem RapidScalarFourier.directional {b : Frequency → ℂ}
    (hb : RapidScalarFourier b) (y : Vec) :
    RapidScalarFourier (fun k => fourierPhaseCLM k y * b k) := by
  intro m
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    (fun k => ?_) ((hb (m + 1)).mul_left ‖y‖)
  calc
    _ = ‖fourierPhaseCLM k y‖ * ‖b k‖ * ‖fourierPhaseCLM k‖ ^ m := by
      rw [norm_mul]
    _ ≤ (‖fourierPhaseCLM k‖ * ‖y‖) * ‖b k‖ * ‖fourierPhaseCLM k‖ ^ m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((fourierPhaseCLM k).le_opNorm y) (norm_nonneg _))
        (pow_nonneg (norm_nonneg _) _)
    _ = ‖y‖ * (‖b k‖ * ‖fourierPhaseCLM k‖ ^ (m + 1)) := by
      rw [pow_succ]
      ring

/-- Smoothness at each finite order follows by differentiating the actual sum. -/
theorem scalarFourierSeries_contDiff_nat (n : ℕ) (b : Frequency → ℂ)
    (hb : RapidScalarFourier b) : ContDiff ℝ n (scalarFourierSeries b) := by
  induction n generalizing b with
  | zero => exact contDiff_zero.mpr (scalarFourierSeries_continuous hb.summable_norm)
  | succ n ih =>
      change ContDiff ℝ ((n : ℕ∞ω) + 1) (scalarFourierSeries b)
      apply contDiff_succ_iff_fderiv_apply.mpr
      refine ⟨fun x => (scalarFourierSeries_hasFDerivAt
        hb.summable_norm hb.summable_first x).differentiableAt, ?_, ?_⟩
      · simp
      · intro y
        have heq : (fun x => fderiv ℝ (scalarFourierSeries b) x y) =
            scalarFourierSeries (fun k => fourierPhaseCLM k y * b k) := by
          funext x
          exact scalarFourierSeries_fderiv_apply hb.summable_norm hb.summable_first x y
        rw [heq]
        exact ih _ (hb.directional y)

theorem scalarFourierSeries_contDiff {b : Frequency → ℂ}
    (hb : RapidScalarFourier b) : ContDiff ℝ ∞ (scalarFourierSeries b) :=
  contDiff_infty.mpr (fun n => scalarFourierSeries_contDiff_nat n b hb)

theorem realFourierSeries_contDiff {b : Frequency → ℂ}
    (hb : RapidScalarFourier b) : ContDiff ℝ ∞ (realFourierSeries b) :=
  Complex.reCLM.contDiff.comp (scalarFourierSeries_contDiff hb)

theorem realFourierSeries_periodic (b : Frequency → ℂ) :
    SpatialPeriodic (realFourierSeries b) := by
  intro x j
  exact congrArg Complex.re (scalarFourierSeries_periodic b x j)

/-- The mean is the actual zero Fourier coefficient, with justified integral interchange. -/
theorem scalarFourierSeries_integral {b : Frequency → ℂ}
    (hb : Summable (fun k => ‖b k‖)) :
    (∫ x in unitCube, scalarFourierSeries b x) = b 0 := by
  have hint (k : Frequency) : IntegrableOn
      (fun x : Vec => fourierCharacter k x * b k) unitCube volume :=
    ((fourierCharacter_contDiff k).continuous.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hnorm : Summable (fun k : Frequency =>
      ∫ x in unitCube, ‖fourierCharacter k x * b k‖) := by
    simpa only [norm_mul, fourierCharacter_norm, one_mul, setIntegral_const, smul_eq_mul]
      using hb.mul_left (volume.real unitCube)
  calc
    _ = ∑' k : Frequency, ∫ x in unitCube, fourierCharacter k x * b k :=
      (integral_tsum_of_summable_integral_norm hint hnorm).symm
    _ = ∑' k : Frequency, if k = 0 then b 0 else 0 := by
      apply tsum_congr
      intro k
      rw [integral_mul_const, integral_fourierCharacter]
      split_ifs with hk
      · simp [hk]
      · simp
    _ = b 0 := by simp

theorem realFourierSeries_meanZero {b : Frequency → ℂ}
    (hb : Summable (fun k => ‖b k‖)) (hzero : b 0 = 0) :
    PressureMeanZero (realFourierSeries b) := by
  have hint : IntegrableOn (scalarFourierSeries b) unitCube volume :=
    (scalarFourierSeries_continuous hb).continuousOn.integrableOn_compact isCompact_unitCube
  refine ⟨Complex.reCLM.integrable_comp hint, ?_⟩
  calc
    _ = (∫ x in unitCube, scalarFourierSeries b x).re :=
      Complex.reCLM.integral_comp_comm hint
    _ = 0 := by rw [scalarFourierSeries_integral hb, hzero]; rfl

/-- The actual physical gradient has the expected convergent coordinate Fourier series. -/
theorem realFourierSeries_gradient_apply {b : Frequency → ℂ}
    (hzero : Summable (fun k => ‖b k‖))
    (hone : Summable (fun k => ‖b k‖ * ‖fourierPhaseCLM k‖))
    (x : Vec) (i : Fin 3) :
    gradient (realFourierSeries b) x i =
      (∑' k : Frequency, fourierCharacter k x * (derivativeSymbol i k * b k)).re := by
  have hd := (scalarFourierSeries_hasFDerivAt hzero hone x).differentiableAt
  have hr : fderiv ℝ (realFourierSeries b) x =
      Complex.reCLM.comp (fderiv ℝ (scalarFourierSeries b) x) :=
    (Complex.reCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (realFourierSeries b) x (unitVector i) = _
  rw [hr]
  change (fderiv ℝ (scalarFourierSeries b) x (unitVector i)).re = _
  rw [scalarFourierSeries_fderiv_apply hzero hone]
  unfold scalarFourierSeries
  congr 1
  apply tsum_congr
  intro k
  change fourierCharacter k x * (fourierPhaseCLM k (unitVector i) * b k) =
    fourierCharacter k x * (derivativeSymbol i k * b k)
  rw [fourierPhaseCLM_unitVector]

end

end SingularClosure
