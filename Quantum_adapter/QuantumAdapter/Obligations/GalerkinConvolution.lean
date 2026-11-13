import QuantumAdapter.Obligations.GalerkinSobolev
import SingularClosure.LatticeSobolevSummability

/-! Cutoff-independent finite convolution and weighted coefficient estimates.
These are the product-estimate ingredients for the viscous all-order argument.
All sums retain the zero Fourier mode. -/

set_option autoImplicit false
set_option Elab.async true
open scoped BigOperators

namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

theorem finite_weighted_cauchy {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i ∈ S, a i * b i) ^ 2 ≤
      (∑ i ∈ S, a i) * ∑ i ∈ S, a i * b i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (a i) * b i)
  have hcancel (i : ι) :
      Real.sqrt (a i) * (Real.sqrt (a i) * b i) = a i * b i := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (ha i)]
  simp_rw [hcancel, mul_pow, Real.sq_sqrt (ha _)] at h
  exact h

theorem finite_shift_square_sum_le (S : Finset Frequency)
    (b : Frequency → ℝ) (hb : ∀ k, k ∉ S → b k = 0) (p : Frequency) :
    (∑ k ∈ S, b (k - p) ^ 2) ≤ ∑ k ∈ S, b k ^ 2 := by
  classical
  let T := S.image (fun k => k - p)
  have he : (∑ k ∈ S, b (k - p) ^ 2) = ∑ k ∈ T, b k ^ 2 := by
    rw [Finset.sum_image]
    intro k hk l hl h
    exact sub_right_cancel h
  have hu : (∑ k ∈ S ∪ T, b k ^ 2) = ∑ k ∈ S, b k ^ 2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro k hk hnot
    rw [hb k hnot]
    simp
  rw [he, ← hu]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun k hk hnot => sq_nonneg _)

theorem finite_shift_sum_le (S : Finset Frequency)
    (b : Frequency → ℝ) (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k, k ∉ S → b k = 0) (p : Frequency) :
    (∑ k ∈ S, b (k - p)) ≤ ∑ k ∈ S, b k := by
  classical
  let T := S.image (fun k => k - p)
  have he : (∑ k ∈ S, b (k - p)) = ∑ k ∈ T, b k := by
    rw [Finset.sum_image]
    intro k hk l hl h
    exact sub_right_cancel h
  have hu : (∑ k ∈ S ∪ T, b k) = ∑ k ∈ S, b k := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro k hk hnot
    exact hb k hnot
  rw [he, ← hu]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun k hk hnot => hb0 k)

theorem finite_reflection_sum_le (S : Finset Frequency)
    (b : Frequency → ℝ) (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k, k ∉ S → b k = 0) (k : Frequency) :
    (∑ p ∈ S, b (k-p)) ≤ ∑ p ∈ S, b p := by
  classical
  let T := S.image (fun p => k-p)
  have he : (∑ p ∈ S, b (k-p)) = ∑ p ∈ T, b p := by
    rw [Finset.sum_image]
    intro p hp q hq h
    exact sub_left_cancel h
  have hu : (∑ p ∈ S ∪ T, b p) = ∑ p ∈ S, b p := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hnot
    exact hb p hnot
  rw [he, ← hu]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun p hp hnot => hb0 p)

/-- Finite Young inequality, with no cardinality-dependent constant. -/
theorem finite_convolution_square_sum_le (S : Finset Frequency)
    (a b : Frequency → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hb : ∀ k, k ∉ S → b k = 0) :
    (∑ k ∈ S, (∑ p ∈ S, a p * b (k - p)) ^ 2) ≤
      (∑ p ∈ S, a p) ^ 2 * ∑ k ∈ S, b k ^ 2 := by
  have hA : 0 ≤ ∑ p ∈ S, a p := Finset.sum_nonneg (fun p hp => ha p)
  calc
    _ ≤ ∑ k ∈ S, (∑ p ∈ S, a p) * ∑ p ∈ S, a p * b (k - p) ^ 2 :=
      Finset.sum_le_sum (fun k hk => finite_weighted_cauchy S a (fun p => b (k-p)) ha)
    _ = (∑ p ∈ S, a p) * ∑ p ∈ S, a p * ∑ k ∈ S, b (k-p) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ (∑ p ∈ S, a p) * ∑ p ∈ S, a p * ∑ k ∈ S, b k ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (finite_shift_square_sum_le S b hb p) (ha p)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The other finite Young orientation, obtained without changing supports. -/
theorem finite_convolution_square_sum_le_right (S : Finset Frequency)
    (a b : Frequency → ℝ) (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k, k ∉ S → b k = 0) :
    (∑ k ∈ S, (∑ p ∈ S, a p * b (k-p)) ^ 2) ≤
      (∑ p ∈ S, b p) ^ 2 * ∑ k ∈ S, a k ^ 2 := by
  have hB : 0 ≤ ∑ p ∈ S, b p := Finset.sum_nonneg (fun p hp => hb0 p)
  have hpoint (k : Frequency) :
      (∑ p ∈ S, a p * b (k-p)) ^ 2 ≤
        (∑ p ∈ S, b p) * ∑ p ∈ S, b (k-p) * a p ^ 2 := by
    have h := finite_weighted_cauchy S (fun p => b (k-p)) a (fun p => hb0 (k-p))
    simp_rw [mul_comm (b (k-_)) (a _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (finite_reflection_sum_le S b hb0 hb k)
      (Finset.sum_nonneg (fun p hp => mul_nonneg (hb0 _) (sq_nonneg _))))
  calc
    _ ≤ ∑ k ∈ S, (∑ p ∈ S, b p) * ∑ p ∈ S, b (k-p) * a p ^ 2 :=
      Finset.sum_le_sum (fun k hk => hpoint k)
    _ = (∑ p ∈ S, b p) * ∑ p ∈ S, a p ^ 2 * ∑ k ∈ S, b (k-p) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (∑ p ∈ S, b p) * ∑ p ∈ S, a p ^ 2 * ∑ k ∈ S, b k := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (finite_shift_sum_le S b hb0 hb p) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Literal scalar weighted coefficient sum, including the zero mode. -/
def coefficientMoment (s N : ℕ) (q : Phase N) : ℝ :=
  ∑ i : Fin 3, ∑ k ∈ fullModes N, torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖

theorem coefficientMoment_nonneg (s N : ℕ) (q : Phase N) :
    0 ≤ coefficientMoment s N q := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro k hk
  positivity

theorem weighted_component_l1_sq_le (s N : ℕ) (q : Phase N) (i : Fin 3) :
    (∑ k ∈ fullModes N, torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖) ^ 2 ≤
      latticeSobolevConstant * ∑ k ∈ fullModes N,
        ‖sobolevWeightedCoeff (s + 2) (phaseCoeff q) (k, i)‖ ^ 2 := by
  have h := finite_l1_sq_le_H2_sq (fullModes N)
    (fun k => (torusSobolevWeight k : ℂ) ^ s * phaseCoeff q k i)
  have hn (k : Frequency) :
      ‖(torusSobolevWeight k : ℂ) ^ s * phaseCoeff q k i‖ =
        torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (torusSobolevWeight_pos k)]
  have hw (k : Frequency) :
      torusSobolevWeight k ^ 2 * (torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖) =
        ‖sobolevWeightedCoeff (s+2) (phaseCoeff q) (k,i)‖ := by
    rw [sobolevWeightedCoeff_norm_eq, pow_add]
    ring
  simp_rw [hn, hw] at h
  exact h

/-- The H(s+2) to weighted-l1 estimate is uniform in N. -/
theorem coefficientMoment_sq_le (s N : ℕ) (q : Phase N) :
    coefficientMoment s N q ^ 2 ≤
      3 * latticeSobolevConstant * sobolevEnergy (s + 2) N q := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun _ => (1 : ℝ))
    (fun i => ∑ k ∈ fullModes N, torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  calc
    _ ≤ 3 * ∑ i : Fin 3,
        (∑ k ∈ fullModes N, torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖) ^ 2 := h
    _ ≤ 3 * ∑ i : Fin 3, latticeSobolevConstant * ∑ k ∈ fullModes N,
        ‖sobolevWeightedCoeff (s+2) (phaseCoeff q) (k,i)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun i hi => weighted_component_l1_sq_le s N q i)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [sobolevEnergy, sobolevEnergyDensity]
      ring

theorem coefficientMoment_le (s N : ℕ) (q : Phase N) :
    coefficientMoment s N q ≤ Real.sqrt (3 * latticeSobolevConstant) *
      Real.sqrt (sobolevEnergy (s + 2) N q) := by
  have h := Real.sqrt_le_sqrt (coefficientMoment_sq_le s N q)
  rw [Real.sqrt_sq (coefficientMoment_nonneg s N q),
    Real.sqrt_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      latticeSobolevConstant_pos.le)] at h
  exact h

theorem first_coefficientMoment_le_h3 (N : ℕ) (q : Phase N) :
    coefficientMoment 1 N q ≤ Real.sqrt (3 * latticeSobolevConstant) *
      Real.sqrt (energy3 N q) := by
  simpa only [show 1+2=3 from rfl, sobolevEnergy_three] using coefficientMoment_le 1 N q

end
end QuantumAdapter.Obligations
