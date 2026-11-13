import GRAdapter.LiteratureInputs
import GRAdapter.UnitTorus

/-!
# Actual cosine/Fourier normalization bridge

The native cosine integral is the real part of a single complex Fourier
mode. No factor two is inserted. These identities use the actual unit-cube
integral and the actual character in `LiteratureInputs`.

Continuity supplies the integrability needed for taking a real part through
the integral. Taking a real part through the infinite series retains an
explicit complex summability hypothesis. Analytic coefficient decay and
Poisson inversion are not inferred from the identities alone.
-/

set_option autoImplicit false

namespace NSEGR

open Set Filter MeasureTheory
open scoped BigOperators

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

end

end NSEGR
