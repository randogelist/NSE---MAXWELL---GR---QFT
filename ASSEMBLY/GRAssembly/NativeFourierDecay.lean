import GRAssembly.NativeFourierCalculus

/-! Product-coordinate decay of actual Fourier coefficients in every finite dimension. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEGR.NativeLiterature
noncomputable section

variable {n : ℕ}

def frequencyWeight (l : ℤ) : ℝ := 1 + (2 * Real.pi * (l : ℝ)) ^ 2

def productWeight (k : LiteratureFrequency n) : ℝ :=
  ∏ j : Fin n, (frequencyWeight (k j))⁻¹

theorem frequencyWeight_pos (l : ℤ) : 0 < frequencyWeight l := by
  unfold frequencyWeight
  positivity

theorem productWeight_nonneg (k : LiteratureFrequency n) : 0 ≤ productWeight k :=
  Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (frequencyWeight_pos (k j)).le)

theorem summable_inverse_frequencyWeight :
    Summable (fun l : ℤ => (frequencyWeight l)⁻¹) := by
  have hp : Summable (fun l : ℤ => (1 : ℝ) / (l : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hz : Summable (fun l : ℤ => if l = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  apply Summable.of_nonneg_of_le
    (fun l => inv_nonneg.mpr (frequencyWeight_pos l).le) _ (hz.add hp)
  intro l
  by_cases hl : l = 0
  · simp [hl, frequencyWeight]
  · have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
    have hsq : 0 < (l : ℝ) ^ 2 := sq_pos_of_ne_zero hlr
    have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hmul := mul_le_mul_of_nonneg_right hpi (sq_nonneg (l : ℝ))
    have hden : (l : ℝ) ^ 2 ≤ frequencyWeight l := by
      unfold frequencyWeight
      nlinarith [hmul]
    simpa only [hl, if_false, zero_add, one_div] using
      (one_div_le_one_div_of_le hsq hden)

private def frequencySplit (m : ℕ) :
    LiteratureFrequency (m + 1) ≃ ℤ × LiteratureFrequency m where
  toFun k := (k 0, fun j => k j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv k := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  right_inv p := by
    rcases p with ⟨a, k⟩
    simp

theorem summable_productWeight (n : ℕ) :
    Summable (fun k : LiteratureFrequency n => productWeight k) := by
  induction n with
  | zero =>
      letI : Fintype (LiteratureFrequency 0) := Fintype.ofSubsingleton (fun i => Fin.elim0 i)
      exact (hasSum_fintype _).summable
  | succ m ih =>
      have hp := summable_inverse_frequencyWeight.mul_of_nonneg ih
        (fun l => inv_nonneg.mpr (frequencyWeight_pos l).le) productWeight_nonneg
      have hi := hp.comp_injective (frequencySplit m).injective
      exact hi.congr (fun k => by
        simp [Function.comp_def, frequencySplit, productWeight, Fin.prod_univ_succ])

def coordinateHelmholtz (j : Fin n) (f : LiteratureSpace n → ℂ) :
    LiteratureSpace n → ℂ :=
  fun x => f x - coordinateDerivative (coordinateDerivative f j) j x

def productHelmholtz : List (Fin n) → (LiteratureSpace n → ℂ) → LiteratureSpace n → ℂ
  | [], f => f
  | j :: js, f => coordinateHelmholtz j (productHelmholtz js f)

theorem coordinateHelmholtz_contDiff {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin n) : ContDiff ℝ ∞ (coordinateHelmholtz j f) :=
  hf.sub (coordinateDerivative_contDiff (coordinateDerivative_contDiff hf j) j)

theorem coordinateHelmholtz_periodic {f : LiteratureSpace n → ℂ}
    (hp : LiteraturePeriodic f) (j : Fin n) : LiteraturePeriodic (coordinateHelmholtz j f) := by
  intro x i
  unfold coordinateHelmholtz
  rw [hp x i,
    coordinateDerivative_periodic (coordinateDerivative_periodic hp j) j x i]

theorem productHelmholtz_contDiff {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (js : List (Fin n)) :
    ContDiff ℝ ∞ (productHelmholtz js f) := by
  induction js with
  | nil => exact hf
  | cons j js ih => exact coordinateHelmholtz_contDiff ih j

theorem productHelmholtz_periodic {f : LiteratureSpace n → ℂ}
    (hp : LiteraturePeriodic f) (js : List (Fin n)) :
    LiteraturePeriodic (productHelmholtz js f) := by
  induction js with
  | nil => exact hp
  | cons j js ih => exact coordinateHelmholtz_periodic ih j

theorem fourierCoefficient_sub {f g : LiteratureSpace n → ℂ}
    (hf : Continuous f) (hg : Continuous g) (k : LiteratureFrequency n) :
    LiteratureFourierCoefficient (fun x => f x - g x) k =
      LiteratureFourierCoefficient f k - LiteratureFourierCoefficient g k := by
  unfold LiteratureFourierCoefficient
  simp_rw [sub_mul]
  exact integral_sub (fourierIntegrand_integrableOn hf k) (fourierIntegrand_integrableOn hg k)

theorem one_sub_derivativeSymbol_sq (j : Fin n) (k : LiteratureFrequency n) :
    1 - derivativeSymbol j k ^ 2 = (frequencyWeight (k j) : ℂ) := by
  have heq : derivativeSymbol j k =
      ((2 * Real.pi * (k j : ℝ) : ℝ) : ℂ) * Complex.I := by
    unfold derivativeSymbol
    push_cast
    ring
  rw [heq, mul_pow, Complex.I_sq]
  unfold frequencyWeight
  push_cast
  ring

theorem fourierCoefficient_coordinateHelmholtz {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f)
    (j : Fin n) (k : LiteratureFrequency n) :
    LiteratureFourierCoefficient (coordinateHelmholtz j f) k =
      (frequencyWeight (k j) : ℂ) * LiteratureFourierCoefficient f k := by
  change LiteratureFourierCoefficient
    (fun x => f x - coordinateDerivative (coordinateDerivative f j) j x) k = _
  rw [fourierCoefficient_sub hf.continuous
    (coordinateDerivative_contDiff (coordinateDerivative_contDiff hf j) j).continuous,
    fourierCoefficient_coordinateDerivative (coordinateDerivative_contDiff hf j)
      (coordinateDerivative_periodic hp j),
    fourierCoefficient_coordinateDerivative hf hp]
  calc
    _ = (1 - derivativeSymbol j k ^ 2) * LiteratureFourierCoefficient f k := by ring
    _ = _ := by rw [one_sub_derivativeSymbol_sq]

theorem fourierCoefficient_productHelmholtz {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f)
    (js : List (Fin n)) (k : LiteratureFrequency n) :
    LiteratureFourierCoefficient (productHelmholtz js f) k =
      (((js.map (fun j => frequencyWeight (k j))).prod : ℝ) : ℂ) *
        LiteratureFourierCoefficient f k := by
  induction js with
  | nil => simp [productHelmholtz]
  | cons j js ih =>
      rw [productHelmholtz,
        fourierCoefficient_coordinateHelmholtz (productHelmholtz_contDiff hf js)
          (productHelmholtz_periodic hp js), ih]
      simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul]
      ring

def productDecayConstant (f : LiteratureSpace n → ℂ) : ℝ :=
  ∫ x in LiteratureUnitCube n, ‖productHelmholtz (List.finRange n) f x‖

theorem productDecayConstant_nonneg (f : LiteratureSpace n → ℂ) :
    0 ≤ productDecayConstant f := integral_nonneg (fun _ => norm_nonneg _)

theorem fourierCoefficient_product_decay {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f) (k : LiteratureFrequency n) :
    ‖LiteratureFourierCoefficient f k‖ ≤ productDecayConstant f * productWeight k := by
  have hg := fourierCoefficient_productHelmholtz hf hp (List.finRange n) k
  have hprod : ((List.finRange n).map (fun j => frequencyWeight (k j))).prod =
      ∏ j : Fin n, frequencyWeight (k j) := (Fin.prod_univ_def _).symm
  rw [hprod] at hg
  have hpos : 0 < ∏ j : Fin n, frequencyWeight (k j) :=
    Finset.prod_pos (fun j _ => frequencyWeight_pos (k j))
  have hb := fourierCoefficient_norm_le_integral_norm
    (productHelmholtz (List.finRange n) f) k
  rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hb
  have hdiv : ‖LiteratureFourierCoefficient f k‖ ≤
      productDecayConstant f / (∏ j : Fin n, frequencyWeight (k j)) := by
    apply (le_div_iff₀ hpos).mpr
    simpa only [productDecayConstant, mul_comm] using hb
  simpa only [div_eq_mul_inv, productWeight, Finset.prod_inv_distrib] using hdiv

theorem summable_norm_fourierCoefficient {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f) :
    Summable (fun k : LiteratureFrequency n => ‖LiteratureFourierCoefficient f k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fourierCoefficient_product_decay hf hp)
    ((summable_productWeight n).mul_left (productDecayConstant f))

theorem summable_norm_fourierCoefficient_partialWord {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f) (w : List (Fin n)) :
    Summable (fun k : LiteratureFrequency n =>
      ‖LiteratureFourierWordMultiplier w k * LiteratureFourierCoefficient f k‖) := by
  have h := summable_norm_fourierCoefficient
    (partialWord_contDiff hf w) (partialWord_periodic hp w)
  simpa only [fourierCoefficient_partialWord hf hp] using h

end
end NSEGR.NativeLiterature
