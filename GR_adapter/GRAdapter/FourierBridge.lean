import GRAdapter.LiteratureInputs
import GRAdapter.UnitTorus

/-!
# Actual cosine/Fourier normalization bridge

The native cosine integral is the real part of a single complex Fourier
mode. No factor two is inserted. These identities use the actual unit-cube
integral and the actual character in `LiteratureInputs`.

Continuity supplies the integrability needed for taking a real part through
the integral. The base series identity retains explicit summability;
the final theorems derive that summability from LI03 for smooth periodic
data. Analytic parameter estimates and Poisson inversion remain separate.
-/

set_option autoImplicit false

namespace NSEGR

open Set Filter MeasureTheory
open scoped BigOperators ContDiff

noncomputable section

def fourierPhase (k : Frequency) (x : Vec) : ℝ :=
  2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) * x i

theorem literatureCharacter_eq_exp_phase (k : Frequency) (x : Vec) :
    LiteratureCharacter k x = Complex.exp ((fourierPhase k x : ℂ) * Complex.I) := by
  unfold LiteratureCharacter fourierPhase
  congr 1
  push_cast
  ring

theorem fourierPhase_neg (k : Frequency) (x : Vec) :
    fourierPhase (-k) x = -fourierPhase k x := by
  simp [fourierPhase, Finset.sum_neg_distrib]

theorem fourierPhase_sub (k : Frequency) (x y : Vec) :
    fourierPhase k (x - y) = fourierPhase k x - fourierPhase k y := by
  simp only [fourierPhase, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem literatureCharacter_mul_negative (k : Frequency) (x y : Vec) :
    LiteratureCharacter k x * LiteratureCharacter (-k) y =
      LiteratureCharacter k (x - y) := by
  rw [literatureCharacter_eq_exp_phase, literatureCharacter_eq_exp_phase,
    literatureCharacter_eq_exp_phase, ← Complex.exp_add, fourierPhase_neg,
    fourierPhase_sub]
  congr 1
  push_cast
  ring

theorem cosineKernel_eq_re_character (k : Frequency) (x y : Vec) :
    cosineKernel k x y =
      (LiteratureCharacter k x * LiteratureCharacter (-k) y).re := by
  rw [literatureCharacter_mul_negative, literatureCharacter_eq_exp_phase,
    Complex.exp_ofReal_mul_I_re]
  simp only [cosineKernel, fourierPhase, PiLp.sub_apply]

theorem literatureCharacter_continuous (k : Frequency) :
    Continuous (fun x : Vec => LiteratureCharacter k x) := by
  unfold LiteratureCharacter
  fun_prop

/-- Exact real-cosine coefficient pairing with the actual complex integral. -/
theorem cosineKernel_integral_eq_re_fourier (f : ScalarField) (hf : Continuous f)
    (k : Frequency) (x : Vec) :
    (∫ y in unitCube, cosineKernel k x y * f y) =
      (LiteratureCharacter k x *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k).re := by
  have hfc : Continuous (fun y : Vec => (f y : ℂ)) :=
    Complex.continuous_ofReal.comp hf
  have hint : IntegrableOn
      (fun y : Vec => LiteratureCharacter k x *
        ((f y : ℂ) * LiteratureCharacter (-k) y)) unitCube :=
    integrableOn_unitCube_of_continuous
      (continuous_const.mul (hfc.mul (literatureCharacter_continuous (-k))))
  have hpoint (y : Vec) :
      (LiteratureCharacter k x * ((f y : ℂ) * LiteratureCharacter (-k) y)).re =
        cosineKernel k x y * f y := by
    calc
      _ = ((LiteratureCharacter k x * LiteratureCharacter (-k) y) * (f y : ℂ)).re := by
        congr 1
        ring
      _ = (LiteratureCharacter k x * LiteratureCharacter (-k) y).re * f y := by simp
      _ = cosineKernel k x y * f y := by rw [← cosineKernel_eq_re_character]
  calc
    (∫ y in unitCube, cosineKernel k x y * f y) =
        ∫ y in unitCube,
          (LiteratureCharacter k x * ((f y : ℂ) * LiteratureCharacter (-k) y)).re := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => (hpoint y).symm)
    _ = (∫ y in unitCube,
          LiteratureCharacter k x * ((f y : ℂ) * LiteratureCharacter (-k) y)).re :=
      integral_re hint
    _ = (LiteratureCharacter k x *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k).re := by
      rw [integral_const_mul]
      rfl

/-- This equality of total series needs no summability premise: both sides
have exactly equal real summands. It does not assert series convergence. -/
theorem poissonInverse_eq_tsum_fourier_re (f : ScalarField) (hf : Continuous f)
    (x : Vec) :
    poissonInverse f x = ∑' k : Frequency, poissonSymbol k *
      (LiteratureCharacter k x *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k).re := by
  unfold poissonInverse
  apply tsum_congr
  intro k
  rw [cosineKernel_integral_eq_re_fourier f hf]

/-- The real part may be taken outside the complex Fourier series precisely
under the displayed summability premise. -/
theorem poissonInverse_eq_re_tsum_fourier (f : ScalarField) (hf : Continuous f)
    (x : Vec)
    (hs : Summable (fun k : Frequency => (poissonSymbol k : ℂ) *
      (LiteratureCharacter k x *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k))) :
    poissonInverse f x =
      (∑' k : Frequency, (poissonSymbol k : ℂ) *
        (LiteratureCharacter k x *
          LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k)).re := by
  rw [poissonInverse_eq_tsum_fourier_re f hf, Complex.re_tsum hs]
  apply tsum_congr
  intro k
  simp

/-- A nonzero integer frequency has squared Euclidean length at least one. -/
theorem frequency_square_sum_ge_one (k : Frequency) (hk : k ≠ 0) :
    1 ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  classical
  have hi : ∃ i : Fin 3, k i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hk
    funext i
    exact h i
  rcases hi with ⟨i, hi⟩
  have hsq : (0 : ℤ) < (k i) ^ 2 := sq_pos_of_ne_zero hi
  have hsq' : (1 : ℤ) ≤ (k i) ^ 2 := by omega
  have hreal : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by exact_mod_cast hsq'
  exact hreal.trans (Finset.single_le_sum
    (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i))

/-- Uniform bound for the actual native Poisson multiplier, including k=0. -/
theorem poissonSymbol_abs_le_one (k : Frequency) : |poissonSymbol k| ≤ 1 := by
  by_cases hk : k = 0
  · simp [poissonSymbol, hk]
  · have hsum := frequency_square_sum_ge_one k hk
    have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hden : (1 : ℝ) ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
      calc
        1 ≤ 4 * Real.pi ^ 2 := hpi
        _ = (4 * Real.pi ^ 2) * 1 := (mul_one _).symm
        _ ≤ (4 * Real.pi ^ 2) * ∑ i : Fin 3, (k i : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    have hdenpos : 0 < 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 :=
      zero_lt_one.trans_le hden
    rw [poissonSymbol, if_neg hk, abs_neg, abs_of_nonneg (inv_nonneg.mpr hdenpos.le)]
    exact (inv_le_one₀ hdenpos).mpr hden

theorem literatureCharacter_norm (k : Frequency) (x : Vec) :
    ‖LiteratureCharacter k x‖ = 1 := by
  rw [literatureCharacter_eq_exp_phase, Complex.norm_exp_ofReal_mul_I]

/-- LI03 supplies absolute summability of the actual period-one Fourier
coefficients of a smooth periodic real field, without a new admission. -/
theorem literatureFourierCoefficient_summable_norm
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    Summable (fun k : Frequency =>
      ‖LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k‖) := by
  have hfc : ContDiff ℝ ∞ (fun y : Vec => (f y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hpc : LiteraturePeriodic (fun y : Vec => (f y : ℂ)) := by
    intro x i
    change (f (x + unitVector i) : ℂ) = (f x : ℂ)
    rw [hp x i]
  have hs := (L.reconstruct 3 (by decide) (fun y : Vec => (f y : ℂ)) hfc hpc []).2.1
  simpa [LiteratureFourierWordMultiplier] using hs

/-- Absolute convergence of the concrete complex Poisson series follows
from LI03 and smooth periodicity. No additional convergence field is used. -/
theorem poisson_fourier_summable_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    Summable (fun k : Frequency => (poissonSymbol k : ℂ) *
      (LiteratureCharacter k x *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k)) := by
  apply (literatureFourierCoefficient_summable_norm L f hf hp).of_norm_bounded
  intro k
  have hm : ‖(poissonSymbol k : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using poissonSymbol_abs_le_one k
  rw [norm_mul, norm_mul, literatureCharacter_norm, one_mul]
  calc
    _ ≤ 1 * ‖LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k‖ :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ = _ := one_mul _

/-- Convergence of the native real cosine series itself, under exactly LI03
and the displayed smooth-periodic hypotheses. -/
theorem poissonInverse_series_summable_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    Summable (fun k : Frequency => poissonSymbol k *
      (∫ y in unitCube, cosineKernel k x y * f y)) := by
  have hs := poisson_fourier_summable_of_literature L f hf hp x
  have hr := (Complex.hasSum_re hs.hasSum).summable
  apply hr.congr
  intro k
  rw [cosineKernel_integral_eq_re_fourier f hf.continuous]
  simp

/-- LI03 discharges the summability premise of the exact native Fourier
representation. Analytic parameter estimates and Delta inversion remain
separate proof obligations. -/
theorem poissonInverse_eq_re_tsum_fourier_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    poissonInverse f x =
      (∑' k : Frequency, (poissonSymbol k : ℂ) *
        (LiteratureCharacter k x *
          LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k)).re :=
  poissonInverse_eq_re_tsum_fourier f hf.continuous x
    (poisson_fourier_summable_of_literature L f hf hp x)

end

end NSEGR
