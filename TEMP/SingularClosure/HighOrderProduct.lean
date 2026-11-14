import SingularClosure.SobolevMultiplierBasics
import SingularClosure.LatticeSobolevSummability

/-!
# Concrete Fourier weights and finite convolution inequalities

All weights are the actual unit-period weights defining TorusSobolev.
The finite convolution constants are independent of every support and cutoff.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem galerkinFreqSq_add_le (p q : Frequency) :
    galerkinFreqSq (p + q) ≤ 2 * (galerkinFreqSq p + galerkinFreqSq q) := by
  unfold galerkinFreqSq
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (p i + q i) ^ 2 ≤ 2 * (p i) ^ 2 + 2 * (q i) ^ 2
  nlinarith [sq_nonneg (p i - q i)]

theorem torusSobolevWeight_add_sq_le (p q : Frequency) :
    torusSobolevWeight (p + q) ^ 2 ≤
      2 * (torusSobolevWeight p ^ 2 + torusSobolevWeight q ^ 2) := by
  have hfreq : (galerkinFreqSq (p + q) : ℝ) ≤
      2 * ((galerkinFreqSq p : ℝ) + (galerkinFreqSq q : ℝ)) := by
    exact_mod_cast galerkinFreqSq_add_le p q
  rw [torusSobolevWeight_sq, torusSobolevWeight_sq, torusSobolevWeight_sq]
  nlinarith [mul_le_mul_of_nonneg_left hfreq (sq_nonneg (2 * Real.pi))]

theorem torusSobolevWeight_add_le (p q : Frequency) :
    torusSobolevWeight (p + q) ≤ 2 * (torusSobolevWeight p + torusSobolevWeight q) := by
  have hp := (torusSobolevWeight_pos p).le
  have hq := (torusSobolevWeight_pos q).le
  have hsum := (torusSobolevWeight_pos (p + q)).le
  have hsquare := torusSobolevWeight_add_sq_le p q
  apply (sq_le_sq₀ hsum (by positivity)).mp
  nlinarith [mul_nonneg hp hq, sq_nonneg (torusSobolevWeight p),
    sq_nonneg (torusSobolevWeight q)]

/-- The fixed weight constant depends only on the Sobolev order. -/
theorem torusSobolevWeight_add_pow_le (m : ℕ) (p q : Frequency) :
    torusSobolevWeight (p + q) ^ m ≤
      ((2 : ℝ) ^ m * 2 ^ (m - 1)) *
        (torusSobolevWeight p ^ m + torusSobolevWeight q ^ m) := by
  calc
    _ ≤ (2 * (torusSobolevWeight p + torusSobolevWeight q)) ^ m :=
      pow_le_pow_left₀ (torusSobolevWeight_pos (p + q)).le
        (torusSobolevWeight_add_le p q) m
    _ = (2 : ℝ) ^ m * (torusSobolevWeight p + torusSobolevWeight q) ^ m := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ m *
        (2 ^ (m - 1) * (torusSobolevWeight p ^ m + torusSobolevWeight q ^ m)) :=
      mul_le_mul_of_nonneg_left
        (add_pow_le (torusSobolevWeight_pos p).le (torusSobolevWeight_pos q).le m)
        (by positivity)
    _ = _ := by ring

theorem finite_sum_comp_le_of_support
    (s t : Finset Frequency) (f : Frequency → ℝ)
    (hf : ∀ k, 0 ≤ f k) (hsupp : ∀ k, k ∉ t → f k = 0)
    (e : Frequency → Frequency) (he : Function.Injective e) :
    (∑ k ∈ s, f (e k)) ≤ ∑ k ∈ t, f k := by
  classical
  calc
    _ = ∑ k ∈ s.image e, f k := (Finset.sum_image he.injOn).symm
    _ = ∑ k ∈ s.image e ∩ t, f k := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro k hk hnot
      apply hsupp k
      intro hkt
      exact hnot (Finset.mem_inter.mpr ⟨hk, hkt⟩)
    _ ≤ ∑ k ∈ t, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun k _ _ => hf k)

theorem frequency_sub_right_injective (p : Frequency) :
    Function.Injective (fun k : Frequency => k - p) := by
  intro x y h
  calc
    x = (x - p) + p := by abel
    _ = (y - p) + p := congrArg (fun z : Frequency => z + p) h
    _ = y := by abel

theorem frequency_sub_left_injective (k : Frequency) :
    Function.Injective (fun p : Frequency => k - p) := by
  intro x y h
  calc
    x = k - (k - x) := by abel
    _ = k - (k - y) := congrArg (fun z : Frequency => k - z) h
    _ = y := by abel

/-- Finite Young inequality, squared L1-by-L2 form for nonnegative coefficients. -/
theorem finite_real_convolution_young_left
    (r s t : Finset Frequency) (a b : Frequency → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hbsupp : ∀ k, k ∉ t → b k = 0) :
    (∑ k ∈ r, (∑ p ∈ s, a p * b (k - p)) ^ 2) ≤
      (∑ p ∈ s, a p) ^ 2 * ∑ q ∈ t, (b q) ^ 2 := by
  have hpoint (k : Frequency) :
      (∑ p ∈ s, a p * b (k - p)) ^ 2 ≤
        (∑ p ∈ s, a p) * ∑ p ∈ s, a p * (b (k - p)) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun p _ => ha p) (fun p _ => mul_nonneg (ha p) (sq_nonneg _))
    intro p _
    exact le_of_eq (by ring)
  have hshift (p : Frequency) :
      (∑ k ∈ r, (b (k - p)) ^ 2) ≤ ∑ q ∈ t, (b q) ^ 2 :=
    finite_sum_comp_le_of_support r t (fun q => (b q) ^ 2)
      (fun q => sq_nonneg _) (fun q hq => by rw [hbsupp q hq]; norm_num)
      (fun k => k - p) (frequency_sub_right_injective p)
  calc
    _ ≤ ∑ k ∈ r, (∑ p ∈ s, a p) * ∑ p ∈ s, a p * (b (k - p)) ^ 2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (∑ p ∈ s, a p) * ∑ p ∈ s, a p * ∑ k ∈ r, (b (k - p)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ ≤ (∑ p ∈ s, a p) * ∑ p ∈ s, a p * ∑ q ∈ t, (b q) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun p _ => ha p))
      exact Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hshift p) (ha p))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The reverse finite Young bound places the L1 norm on the second factor. -/
theorem finite_real_convolution_young_right
    (r s t : Finset Frequency) (a b : Frequency → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hbsupp : ∀ k, k ∉ t → b k = 0) :
    (∑ k ∈ r, (∑ p ∈ s, a p * b (k - p)) ^ 2) ≤
      (∑ q ∈ t, b q) ^ 2 * ∑ p ∈ s, (a p) ^ 2 := by
  have hpoint (k : Frequency) :
      (∑ p ∈ s, a p * b (k - p)) ^ 2 ≤
        (∑ q ∈ t, b q) * ∑ p ∈ s, b (k - p) * (a p) ^ 2 := by
    have hCS : (∑ p ∈ s, a p * b (k - p)) ^ 2 ≤
        (∑ p ∈ s, b (k - p)) * ∑ p ∈ s, b (k - p) * (a p) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (fun p _ => hb _) (fun p _ => mul_nonneg (hb _) (sq_nonneg _))
      intro p _
      exact le_of_eq (by ring)
    exact hCS.trans (mul_le_mul_of_nonneg_right
      (finite_sum_comp_le_of_support s t b hb hbsupp
        (fun p => k - p) (frequency_sub_left_injective k))
      (Finset.sum_nonneg (fun p _ => mul_nonneg (hb _) (sq_nonneg _))))
  have hshift (p : Frequency) :
      (∑ k ∈ r, b (k - p)) ≤ ∑ q ∈ t, b q :=
    finite_sum_comp_le_of_support r t b hb hbsupp
      (fun k => k - p) (frequency_sub_right_injective p)
  calc
    _ ≤ ∑ k ∈ r, (∑ q ∈ t, b q) * ∑ p ∈ s, b (k - p) * (a p) ^ 2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (∑ q ∈ t, b q) * ∑ p ∈ s, (∑ k ∈ r, b (k - p)) * (a p) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul]
    _ ≤ (∑ q ∈ t, b q) * ∑ p ∈ s, (∑ q ∈ t, b q) * (a p) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun q _ => hb q))
      exact Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hshift p) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Literal finite Fourier convolution of two scalar coefficient families. -/
def finiteScalarConvolution (s : Finset Frequency) (a b : Frequency → ℂ)
    (k : Frequency) : ℂ :=
  ∑ p ∈ s, a p * b (k - p)

theorem finiteScalarConvolution_weighted_norm_le (m : ℕ)
    (s : Finset Frequency) (a b : Frequency → ℂ) (k : Frequency) :
    torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖ ≤
      ((2 : ℝ) ^ m * 2 ^ (m - 1)) *
        ((∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) * ‖b (k - p)‖) +
          ∑ p ∈ s, ‖a p‖ * (torusSobolevWeight (k - p) ^ m * ‖b (k - p)‖)) := by
  have htriangle : ‖finiteScalarConvolution s a b k‖ ≤
      ∑ p ∈ s, ‖a p‖ * ‖b (k - p)‖ := by
    simpa only [finiteScalarConvolution, norm_mul] using
      norm_sum_le s (fun p => a p * b (k - p))
  calc
    _ ≤ torusSobolevWeight k ^ m * ∑ p ∈ s, ‖a p‖ * ‖b (k - p)‖ :=
      mul_le_mul_of_nonneg_left htriangle (pow_nonneg (torusSobolevWeight_pos k).le _)
    _ = ∑ p ∈ s, torusSobolevWeight k ^ m * (‖a p‖ * ‖b (k - p)‖) :=
      Finset.mul_sum ..
    _ ≤ ∑ p ∈ s, (((2 : ℝ) ^ m * 2 ^ (m - 1)) *
        (torusSobolevWeight p ^ m + torusSobolevWeight (k - p) ^ m)) *
          (‖a p‖ * ‖b (k - p)‖) := by
      apply Finset.sum_le_sum
      intro p _
      have hpk : p + (k - p) = k := by abel
      have hw := torusSobolevWeight_add_pow_le m p (k - p)
      rw [hpk] at hw
      exact mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro p hp <;> ring

/-- A concrete high-order finite Fourier product estimate before substituting
the universal H2-to-l1 embedding. There is no cutoff-dependent factor. -/
theorem finiteScalarConvolution_weighted_square_le (m : ℕ)
    (r s t : Finset Frequency) (a b : Frequency → ℂ)
    (hbsupp : ∀ k, k ∉ t → b k = 0) :
    (∑ k ∈ r, (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖) ^ 2) ≤
      (2 * (((2 : ℝ) ^ m * 2 ^ (m - 1)) ^ 2)) *
        (((∑ q ∈ t, ‖b q‖) ^ 2) *
            (∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2) +
          ((∑ p ∈ s, ‖a p‖) ^ 2) *
            (∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2)) := by
  let C : ℝ := (2 : ℝ) ^ m * 2 ^ (m - 1)
  let A : Frequency → ℝ := fun k =>
    ∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) * ‖b (k - p)‖
  let B : Frequency → ℝ := fun k =>
    ∑ p ∈ s, ‖a p‖ * (torusSobolevWeight (k - p) ^ m * ‖b (k - p)‖)
  have hpoint (k : Frequency) :
      (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖) ^ 2 ≤
        2 * C ^ 2 * ((A k) ^ 2 + (B k) ^ 2) := by
    have hw := finiteScalarConvolution_weighted_norm_le m s a b k
    change torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖ ≤
      C * (A k + B k) at hw
    have hs := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _) (norm_nonneg _)) hw 2
    have hsum : (A k + B k) ^ 2 ≤ 2 * ((A k) ^ 2 + (B k) ^ 2) := by
      nlinarith [sq_nonneg (A k - B k)]
    calc
      _ ≤ (C * (A k + B k)) ^ 2 := hs
      _ = C ^ 2 * (A k + B k) ^ 2 := mul_pow ..
      _ ≤ C ^ 2 * (2 * ((A k) ^ 2 + (B k) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  have hA : (∑ k ∈ r, (A k) ^ 2) ≤
      (∑ q ∈ t, ‖b q‖) ^ 2 * ∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2 := by
    apply finite_real_convolution_young_right r s t
      (fun p => torusSobolevWeight p ^ m * ‖a p‖) (fun q => ‖b q‖)
      (fun p => mul_nonneg (pow_nonneg (torusSobolevWeight_pos p).le _) (norm_nonneg _))
      (fun q => norm_nonneg _)
    intro q hq
    rw [hbsupp q hq, norm_zero]
  have hB : (∑ k ∈ r, (B k) ^ 2) ≤
      (∑ p ∈ s, ‖a p‖) ^ 2 * ∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2 := by
    apply finite_real_convolution_young_left r s t
      (fun p => ‖a p‖) (fun q => torusSobolevWeight q ^ m * ‖b q‖)
      (fun p => norm_nonneg _)
      (fun q => mul_nonneg (pow_nonneg (torusSobolevWeight_pos q).le _) (norm_nonneg _))
    intro q hq
    rw [hbsupp q hq, norm_zero, mul_zero]
  calc
    _ ≤ ∑ k ∈ r, 2 * C ^ 2 * ((A k) ^ 2 + (B k) ^ 2) :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (2 * C ^ 2) * ((∑ k ∈ r, (A k) ^ 2) + ∑ k ∈ r, (B k) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)

/-- Actual finite scalar Fourier products satisfy the uniform H2/Hm tame bound.
The output support is arbitrary; the constant depends only on m. -/
theorem FINITE_FOURIER_TAME_PRODUCT_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s t : Finset Frequency, ∀ a b : Frequency → ℂ,
      (∀ k, k ∉ t → b k = 0) →
      (∑ k ∈ r, (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖) ^ 2) ≤
        C *
          ((∑ q ∈ t, (torusSobolevWeight q ^ 2 * ‖b q‖) ^ 2) *
              (∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2) +
            (∑ p ∈ s, (torusSobolevWeight p ^ 2 * ‖a p‖) ^ 2) *
              (∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2)) := by
  let W : ℝ := (2 : ℝ) ^ m * 2 ^ (m - 1)
  refine ⟨2 * W ^ 2 * latticeSobolevConstant, ?_, ?_⟩
  · have hW : 0 < W := by dsimp [W]; positivity
    exact mul_pos (mul_pos (by norm_num) (pow_pos hW 2)) latticeSobolevConstant_pos
  intro r s t a b hbsupp
  have ha := finite_l1_sq_le_H2_sq s a
  have hb := finite_l1_sq_le_H2_sq t b
  have hma : 0 ≤ ∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2 :=
    Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hmb : 0 ≤ ∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2 :=
    Finset.sum_nonneg (fun q _ => sq_nonneg _)
  calc
    _ ≤ (2 * W ^ 2) *
        (((∑ q ∈ t, ‖b q‖) ^ 2) *
            (∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2) +
          ((∑ p ∈ s, ‖a p‖) ^ 2) *
            (∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2)) :=
      finiteScalarConvolution_weighted_square_le m r s t a b hbsupp
    _ ≤ (2 * W ^ 2) *
        ((latticeSobolevConstant *
            (∑ q ∈ t, (torusSobolevWeight q ^ 2 * ‖b q‖) ^ 2)) *
              (∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2) +
          (latticeSobolevConstant *
            (∑ p ∈ s, (torusSobolevWeight p ^ 2 * ‖a p‖) ^ 2)) *
              (∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hb hma)
          (mul_le_mul_of_nonneg_right ha hmb)) (by positivity)
    _ = _ := by ring

end

end SingularClosure
