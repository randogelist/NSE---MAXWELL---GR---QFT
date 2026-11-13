import SingularClosure.InfiniteFourierPressure
import SingularClosure.FourierSobolevOperators
import SingularClosure.SobolevSpacetimeSmooth
import SingularClosure.FourierSobolevRhs

/-! The actual pressure multiplier as a bounded linear map on every Fourier
Sobolev space, and joint spacetime smoothness of the resulting transport
pressure. Scalar coefficients occupy the first vector component. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators ENNReal ContDiff

namespace SingularClosure

noncomputable section

theorem pressureFromTransport_add_arg (k : Frequency) (b d : Fin 3 → ℂ) :
    pressureFromTransport k (b + d) = pressureFromTransport k b + pressureFromTransport k d := by
  by_cases hk : k = 0
  · simp [pressureFromTransport, hk]
  · simp only [pressureFromTransport, if_neg hk, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, add_div] <;> ring

theorem pressureFromTransport_smul_arg (k : Frequency) (z : ℂ) (b : Fin 3 → ℂ) :
    pressureFromTransport k (z • b) = z * pressureFromTransport k b := by
  by_cases hk : k = 0
  · simp [pressureFromTransport, hk]
  · have hsum : (∑ j : Fin 3, (k j : ℂ) * (z * b j)) =
        z * ∑ j : Fin 3, (k j : ℂ) * b j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [pressureFromTransport, if_neg hk, Pi.smul_apply, smul_eq_mul, hsum]
    ring

def pressureVectorCoeff (b : FourierCoeff) : FourierCoeff :=
  fun k i => if i = 0 then pressureFromTransport k (b k) else 0

@[simp]
theorem pressureVectorCoeff_first (b : FourierCoeff) (k : Frequency) :
    pressureVectorCoeff b k 0 = infinitePressureCoefficient b k := by
  simp [pressureVectorCoeff, infinitePressureCoefficient]

@[simp]
theorem pressureVectorCoeff_zero_mode (b : FourierCoeff) (i : Fin 3) :
    pressureVectorCoeff b 0 i = 0 := by
  simp [pressureVectorCoeff, pressureFromTransport]

theorem pressureVectorCoeff_add (b d : FourierCoeff) :
    pressureVectorCoeff (b + d) = pressureVectorCoeff b + pressureVectorCoeff d := by
  funext k i
  by_cases hi : i = 0 <;>
    simp [pressureVectorCoeff, hi, pressureFromTransport_add_arg]

theorem pressureVectorCoeff_smul (z : ℂ) (b : FourierCoeff) :
    pressureVectorCoeff (z • b) = z • pressureVectorCoeff b := by
  funext k i
  by_cases hi : i = 0 <;>
    simp [pressureVectorCoeff, hi, pressureFromTransport_smul_arg]

theorem pressureFromTransport_norm_sq_le (k : Frequency) (b : Fin 3 → ℂ) :
    ‖pressureFromTransport k b‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ‖b i‖ ^ 2 := by
  have hsq := pow_le_pow_left₀ (norm_nonneg _)
    (pressureFromTransport_norm_le k b) 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 3 => ‖b i‖)
  exact hsq.trans (by simpa using hcs)

theorem torusSobolev_pressure_mode_sum_le (s : ℕ) (b : FourierCoeff) (k : Frequency) :
    (∑ i : Fin 3, ‖sobolevWeightedCoeff s (pressureVectorCoeff b) (k, i)‖ ^ 2) ≤
      3 * ∑ i : Fin 3, ‖sobolevWeightedCoeff s b (k, i)‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (pressureFromTransport_norm_sq_le k (b k))
    (sq_nonneg (torusSobolevWeight k ^ s))
  have hleft : (∑ i : Fin 3,
      ‖sobolevWeightedCoeff s (pressureVectorCoeff b) (k, i)‖ ^ 2) =
        (torusSobolevWeight k ^ s * ‖pressureFromTransport k (b k)‖) ^ 2 := by
    classical
    simp [torusSobolev_weightedCoeff_norm, pressureVectorCoeff, Fin.sum_univ_succ]
  rw [hleft]
  simp only [torusSobolev_weightedCoeff_norm, mul_pow, ← Finset.mul_sum]
  nlinarith

theorem torusSobolev_pressure_finite_sum_le (s : ℕ) (b : TorusSobolev s)
    (S : Finset FourierIndex) :
    (∑ ki ∈ S, ‖sobolevWeightedCoeff s (pressureVectorCoeff b.val) ki‖ ^ 2) ≤
      3 * ‖b‖ ^ 2 := by
  classical
  have hsub : S ⊆ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff s (pressureVectorCoeff b.val) ki‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => sq_nonneg _)
    _ = ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s (pressureVectorCoeff b.val) (k, i)‖ ^ 2 :=
      Finset.sum_product (S.image Prod.fst) Finset.univ
        (fun ki : FourierIndex => ‖sobolevWeightedCoeff s (pressureVectorCoeff b.val) ki‖ ^ 2)
    _ ≤ ∑ k ∈ S.image Prod.fst, 3 * ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s b.val (k, i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => torusSobolev_pressure_mode_sum_le s b.val k)
    _ = 3 * ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s b.val (k, i)‖ ^ 2 := (Finset.mul_sum ..).symm
    _ = 3 * ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff s b.val ki‖ ^ 2 :=
      congrArg (fun z : ℝ => 3 * z)
        (Finset.sum_product (S.image Prod.fst) Finset.univ
          (fun ki : FourierIndex => ‖sobolevWeightedCoeff s b.val ki‖ ^ 2)).symm
    _ ≤ 3 * ‖b‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (torusSobolev_finite_weighted_sum_le s b _)
        (by norm_num)

def pressureFourierLinear : FourierCoeff →ₗ[ℂ] FourierCoeff where
  toFun := pressureVectorCoeff
  map_add' := pressureVectorCoeff_add
  map_smul' := pressureVectorCoeff_smul

theorem torusSobolevPressure_mem (s : ℕ) (b : TorusSobolev s) :
    Memℓp (sobolevWeightedCoeff s (pressureFourierLinear b.val)) 2 := by
  change Memℓp (sobolevWeightedCoeff s (pressureVectorCoeff b.val)) 2
  apply memℓp_gen' (C := 3 * ‖b‖ ^ 2)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    torusSobolev_pressure_finite_sum_le s b S

def torusSobolevPressureLinear (s : ℕ) : TorusSobolev s →ₗ[ℂ] TorusSobolev s :=
  torusSobolevLiftLinear s s pressureFourierLinear (torusSobolevPressure_mem s)

@[simp]
theorem torusSobolevPressureLinear_coeff (s : ℕ) (b : TorusSobolev s) :
    (torusSobolevPressureLinear s b).val = pressureVectorCoeff b.val :=
  torusSobolevLiftLinear_coeff s s pressureFourierLinear (torusSobolevPressure_mem s) b

theorem torusSobolevPressureLinear_norm_le (s : ℕ) (b : TorusSobolev s) :
    ‖torusSobolevPressureLinear s b‖ ≤ Real.sqrt 3 * ‖b‖ := by
  calc
    _ = ‖torusSobolevRepr s (torusSobolevPressureLinear s b)‖ :=
      ((torusSobolevRepr s).norm_map _).symm
    _ ≤ Real.sqrt 3 * ‖b‖ := by
      apply lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) (by norm_num)
        (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg b))
      intro S
      simp only [torusSobolevRepr_apply, torusSobolevPressureLinear_coeff]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, sobolevWeightedCoeff,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using
        torusSobolev_pressure_finite_sum_le s b S

/-- The pressure Fourier multiplier is an actual bounded linear Sobolev map. -/
def torusSobolevPressure (s : ℕ) : TorusSobolev s →L[ℂ] TorusSobolev s :=
  (torusSobolevPressureLinear s).mkContinuous (Real.sqrt 3)
    (torusSobolevPressureLinear_norm_le s)

@[simp]
theorem torusSobolevPressure_coeff (s : ℕ) (b : TorusSobolev s) :
    (torusSobolevPressure s b).val = pressureVectorCoeff b.val := by
  unfold torusSobolevPressure
  exact (congrArg (fun v : TorusSobolev s => v.val)
    ((torusSobolevPressureLinear s).mkContinuous_apply (Real.sqrt 3)
      (torusSobolevPressureLinear_norm_le s) b)).trans (torusSobolevPressureLinear_coeff s b)

theorem torusSobolevPressure_norm_sq_le (s : ℕ) (b : TorusSobolev s) :
    ‖torusSobolevPressure s b‖ ^ 2 ≤ 3 * ‖b‖ ^ 2 := by
  have happ : torusSobolevPressure s b = torusSobolevPressureLinear s b := by
    unfold torusSobolevPressure
    exact (torusSobolevPressureLinear s).mkContinuous_apply (Real.sqrt 3)
      (torusSobolevPressureLinear_norm_le s) b
  rw [happ]
  have h := pow_le_pow_left₀ (norm_nonneg _) (torusSobolevPressureLinear_norm_le s b) 2
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using! h

theorem smoothFourierSynthesis_pressureVector_first (b : FourierCoeff) (x : Vec) :
    smoothFourierSynthesis (pressureVectorCoeff b) x 0 = infiniteTransportPressure b x := by
  change (scalarFourierSeries (fun k => pressureVectorCoeff b k 0) x).re = _
  simp only [pressureVectorCoeff_first]
  rfl

/-- Actual pressure curves constructed directly from the untruncated transport. -/
def sobolevTransportPressureCurve (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (s : ℕ) (t : ℝ) : TorusSobolev s :=
  torusSobolevPressure s (sobolevDivergenceProduct s (U (s + 2) t) (U (s + 2) t))

theorem sobolevTransportPressureCurve_contDiffOn
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Ici (0 : ℝ))) (s : ℕ) :
    ContDiffOn ℝ ∞ (sobolevTransportPressureCurve U s) (Ici (0 : ℝ)) := by
  have hprod : ContDiffOn ℝ ∞
      (fun t => sobolevDivergenceProduct s (U (s + 2) t) (U (s + 2) t)) (Ici (0 : ℝ)) :=
    (sobolevDivergenceProduct_diagonal_contDiff s).fun_comp_contDiffOn (hU (s + 2))
  exact ((torusSobolevPressure s).restrictScalars ℝ).contDiff.fun_comp_contDiffOn hprod

theorem sobolevTransportPressureCurve_coeff
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hcoeff : ∀ (s : ℕ) (t : ℝ), 0 ≤ t → (U s t).val = (U 0 t).val)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (sobolevTransportPressureCurve U s t).val =
      pressureVectorCoeff (fullTransportCoefficients (U 0 t)) := by
  have hlower : torusSobolevLower 0 (s + 2) (Nat.zero_le _) (U (s + 2) t) = U 0 t := by
    apply Subtype.ext
    simpa only [torusSobolevLower_coeff] using hcoeff (s + 2) t ht
  rw [sobolevTransportPressureCurve, torusSobolevPressure_coeff, sobolevDivergenceProduct_coeff]
  apply congrArg pressureVectorCoeff
  funext k i
  unfold sobolevDivergenceProductCoeff fullTransportCoefficients
  simp only [hlower]

/-- The actual pressure of the actual infinite transport is jointly smooth
on the full closed nonnegative spacetime domain. -/
theorem SOBOLEV_TRANSPORT_PRESSURE_JOINT_SMOOTH
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Ici (0 : ℝ)))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), 0 ≤ t → (U s t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fullTransportPressure (U 0 z.1) z.2) forwardSpacetime := by
  have hP : ∀ (s : ℕ) (t : ℝ), 0 ≤ t →
      (sobolevTransportPressureCurve U s t).val = (sobolevTransportPressureCurve U 0 t).val := by
    intro s t ht
    rw [sobolevTransportPressureCurve_coeff U hcoeff s t ht,
      sobolevTransportPressureCurve_coeff U hcoeff 0 t ht]
  have hjoint := SOBOLEV_CURVES_JOINT_SPACETIME_SMOOTH
    (sobolevTransportPressureCurve U) (sobolevTransportPressureCurve_contDiffOn U hU) hP
  have hscalar := (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ).contDiff.fun_comp_contDiffOn hjoint
  apply hscalar.congr
  intro z hz
  change fullTransportPressure (U 0 z.1) z.2 =
    smoothFourierSynthesis (sobolevTransportPressureCurve U 0 z.1).val z.2 0
  rw [sobolevTransportPressureCurve_coeff U hcoeff 0 z.1 hz,
    smoothFourierSynthesis_pressureVector_first]
  rfl

end

end SingularClosure
