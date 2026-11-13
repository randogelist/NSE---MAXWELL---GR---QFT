import SingularClosure.InitialCutoffBounds

/-! Finite-order identities and decay for the actual Fourier integrals of smooth fields. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Iteration of the actual Fréchet coordinate derivative. -/
def iteratedCoordinateDerivative (j : Fin 3) : ℕ → Field → Field
  | 0, a => a
  | m + 1, a => coordinateDerivative (iteratedCoordinateDerivative j m a) j

theorem iteratedCoordinateDerivative_smooth (j : Fin 3) (m : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (iteratedCoordinateDerivative j m a) := by
  induction m with
  | zero => exact ha
  | succ m ih => exact (contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const

theorem coordinateDerivative_spatialPeriodic (j : Fin 3) (a : Field)
    (hp : SpatialPeriodic a) : SpatialPeriodic (coordinateDerivative a j) := by
  intro x i
  have heq : (fun y : Vec => a (y + unitVector i)) = a :=
    funext (fun y => hp y i)
  have h := congrArg (fun b : Field => fderiv ℝ b x) heq
  have hd : fderiv ℝ a (x + unitVector i) = fderiv ℝ a x := by
    simpa only [fderiv_comp_add_right] using h
  exact congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector j)) hd

theorem iteratedCoordinateDerivative_spatialPeriodic (j : Fin 3) (m : ℕ) (a : Field)
    (hp : SpatialPeriodic a) : SpatialPeriodic (iteratedCoordinateDerivative j m a) := by
  induction m with
  | zero => exact hp
  | succ m ih => exact coordinateDerivative_spatialPeriodic j _ ih

/-- Every finite derivative order is identified with the literal Fourier multiplier. -/
theorem datumFourierCoeff_iteratedCoordinateDerivative (j : Fin 3) (m : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    datumFourierCoeff (iteratedCoordinateDerivative j m a) =
      spectralMultiplier (fun k => derivativeSymbol j k ^ m) (datumFourierCoeff a) := by
  induction m with
  | zero =>
      funext k i
      simp [iteratedCoordinateDerivative, spectralMultiplier]
  | succ m ih =>
      rw [iteratedCoordinateDerivative,
        datumFourierCoeff_coordinateDerivative j _
          (iteratedCoordinateDerivative_smooth j m a ha)
          (iteratedCoordinateDerivative_spatialPeriodic j m a hp), ih]
      funext k i
      simp only [spectralMultiplier, pow_succ]
      ring

theorem fourierCharacter_norm (k : Frequency) (x : Vec) : ‖fourierCharacter k x‖ = 1 := by
  have hprod : star (fourierCharacter k x) * fourierCharacter k x = 1 := by
    rw [← fourierCharacter_neg, fourierCharacter_mul]
    simp [fourierCharacter]
  have hn := congrArg norm hprod
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg (fourierCharacter k x)]

theorem datumFourierIntegrand_norm (a : Field) (k : Frequency) (i : Fin 3) (x : Vec) :
    ‖datumFourierIntegrand a k i x‖ = ‖a x i‖ := by
  simp only [datumFourierIntegrand, norm_mul, norm_star, fourierCharacter_norm,
    Complex.norm_real, one_mul]

/-- Direct L¹ bound for the physical Fourier integral; no series representation is used. -/
theorem datumFourierCoeff_norm_le_componentL1 (a : Field) (k : Frequency) (i : Fin 3) :
    ‖datumFourierCoeff a k i‖ ≤ ∫ x in unitCube, ‖a x i‖ := by
  calc
    _ ≤ ∫ x in unitCube, ‖datumFourierIntegrand a k i x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp only [datumFourierIntegrand_norm]

theorem derivativeSymbol_norm (j : Fin 3) (k : Frequency) :
    ‖derivativeSymbol j k‖ = (2 * Real.pi) * |(k j : ℝ)| := by
  rw [derivativeSymbol, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)]

/-- The finite constant controlling decay in a fixed coordinate and component. -/
def coordinateDerivativeL1 (j : Fin 3) (m : ℕ) (a : Field) (i : Fin 3) : ℝ :=
  ∫ x in unitCube, ‖iteratedCoordinateDerivative j m a x i‖

theorem coordinateDerivativeL1_nonneg (j : Fin 3) (m : ℕ) (a : Field) (i : Fin 3) :
    0 ≤ coordinateDerivativeL1 j m a i :=
  integral_nonneg (fun x => norm_nonneg _)

theorem iteratedCoordinateDerivative_component_integrable (j : Fin 3) (m : ℕ)
    (a : Field) (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    IntegrableOn (fun x : Vec => ‖iteratedCoordinateDerivative j m a x i‖)
      unitCube volume :=
  (((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
    (iteratedCoordinateDerivative_smooth j m a ha).continuous).norm).continuousOn.integrableOn_compact
      isCompact_unitCube

/-- Arbitrarily high coordinate-frequency decay, proved from repeated physical differentiation. -/
theorem FOURIER_COORDINATE_POWER_BOUND (j : Fin 3) (m : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) (i : Fin 3) :
    ((2 * Real.pi) * |(k j : ℝ)|) ^ m * ‖datumFourierCoeff a k i‖ ≤
      coordinateDerivativeL1 j m a i := by
  have hid : ‖datumFourierCoeff (iteratedCoordinateDerivative j m a) k i‖ =
      ((2 * Real.pi) * |(k j : ℝ)|) ^ m * ‖datumFourierCoeff a k i‖ := by
    rw [datumFourierCoeff_iteratedCoordinateDerivative j m a ha hp]
    simp only [spectralMultiplier, norm_mul, norm_pow, derivativeSymbol_norm]
  rw [← hid]
  exact datumFourierCoeff_norm_le_componentL1 _ k i

/-- Quotient form of the same decay estimate away from the chosen coordinate hyperplane. -/
theorem FOURIER_COORDINATE_DECAY (j : Fin 3) (m : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) (i : Fin 3)
    (hk : k j ≠ 0) :
    ‖datumFourierCoeff a k i‖ ≤
      coordinateDerivativeL1 j m a i / (((2 * Real.pi) * |(k j : ℝ)|) ^ m) := by
  have hk' : (k j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hd : 0 < ((2 * Real.pi) * |(k j : ℝ)|) ^ m :=
    pow_pos (mul_pos (by positivity) (abs_pos.mpr hk')) _
  apply (le_div_iff₀ hd).mpr
  simpa only [mul_comm] using FOURIER_COORDINATE_POWER_BOUND j m a ha hp k i

def fourierDecayConstant (m : ℕ) (a : Field) : ℝ :=
  ∑ i : Fin 3, ((∫ x in unitCube, ‖a x i‖) +
    ∑ j : Fin 3, coordinateDerivativeL1 j m a i)

theorem fourierDecayConstant_nonneg (m : ℕ) (a : Field) :
    0 ≤ fourierDecayConstant m a := by
  unfold fourierDecayConstant
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg (integral_nonneg (fun x => norm_nonneg _))
    (Finset.sum_nonneg (fun j _ => coordinateDerivativeL1_nonneg j m a i))

/-- One finite constant controls every Fourier coefficient and coordinate direction. -/
theorem FOURIER_POLYNOMIAL_WEIGHT_BOUND (m : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) (i : Fin 3) :
    (1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ m) *
        ‖datumFourierCoeff a k i‖ ≤ fourierDecayConstant m a := by
  calc
    _ = ‖datumFourierCoeff a k i‖ +
        ∑ j : Fin 3, (((2 * Real.pi) * |(k j : ℝ)|) ^ m *
          ‖datumFourierCoeff a k i‖) := by rw [add_mul, one_mul, Finset.sum_mul]
    _ ≤ (∫ x in unitCube, ‖a x i‖) +
        ∑ j : Fin 3, coordinateDerivativeL1 j m a i := by
      exact add_le_add (datumFourierCoeff_norm_le_componentL1 a k i)
        (Finset.sum_le_sum (fun j _ => FOURIER_COORDINATE_POWER_BOUND j m a ha hp k i))
    _ ≤ fourierDecayConstant m a := by
      unfold fourierDecayConstant
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun l : Fin 3 => (∫ x in unitCube, ‖a x l‖) +
          ∑ j : Fin 3, coordinateDerivativeL1 j m a l)
        (fun l _ => add_nonneg (integral_nonneg (fun x => norm_nonneg _))
          (Finset.sum_nonneg (fun j _ => coordinateDerivativeL1_nonneg j m a l)))
        (Finset.mem_univ i)

/-- Arbitrary polynomial order, including the zero mode, without any Fourier-series premise. -/
theorem FOURIER_POLYNOMIAL_DECAY (m : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) (i : Fin 3) :
    ‖datumFourierCoeff a k i‖ ≤ fourierDecayConstant m a /
      (1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ m) := by
  have hsum : 0 ≤ ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ m :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) _)
  apply (le_div_iff₀ (by linarith :
    0 < 1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ m)).mpr
  simpa only [mul_comm] using FOURIER_POLYNOMIAL_WEIGHT_BOUND m a ha hp k i

end

end SingularClosure
