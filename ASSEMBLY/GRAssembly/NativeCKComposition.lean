import Mathlib

/-!
Quantitative superposition estimates for positive-degree multilinear series.
The coefficient-space lifting uses these theorems after constructing actual
continuous multilinear maps on the Banach space of symmetric coefficients.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped Topology BigOperators

namespace NSEGR.NativeLiterature

noncomputable section

variable {H B : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Diagonal evaluation of a positive-degree multilinear coefficient is
Lipschitz on a norm ball, with the explicit degree factor. -/
theorem ck_multilinear_diagonal_difference_bound (n : ℕ)
    (c : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    {s : ℝ} (hs : 0 ≤ s) {x y : H} (hx : ‖x‖ ≤ s) (hy : ‖y‖ ≤ s) :
    ‖c (fun _ => x) - c (fun _ => y)‖ ≤
      (‖c‖ * (n + 1) * s ^ n) * ‖x - y‖ := by
  have h := c.norm_image_sub_le (fun _ => x) (fun _ => y)
  simp only [Fintype.card_fin, pi_norm_const, Pi.sub_def, Nat.add_sub_cancel] at h
  calc
    ‖c (fun _ => x) - c (fun _ => y)‖ ≤
      ‖c‖ * (n + 1) * (max ‖x‖ ‖y‖) ^ n * ‖x - y‖ := by
        simpa only [Nat.cast_add, Nat.cast_one] using h
    _ ≤ (‖c‖ * (n + 1) * s ^ n) * ‖x - y‖ := by
      gcongr
      exact max_le hx hy

/-- The corresponding diagonal norm bound, including the zero-radius case. -/
theorem ck_multilinear_diagonal_norm_bound (n : ℕ)
    (c : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    {s : ℝ} (hs : 0 ≤ s) {x : H} (hx : ‖x‖ ≤ s) :
    ‖c (fun _ => x)‖ ≤ (‖c‖ * (n + 1) * s ^ n) * ‖x‖ := by
  have hc₀ : c (fun _ => (0 : H)) = 0 := c.map_zero
  simpa only [hc₀, sub_zero, norm_zero] using ck_multilinear_diagonal_difference_bound n c hs hx
    (show ‖(0 : H)‖ ≤ s by simpa using hs)

/-- Actual sum of positive-degree multilinear diagonal evaluations. -/
def ckPositiveMultilinearSum
    (c : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    (x : H) : B := ∑' n, c n (fun _ => x)

/-- The explicit nonnegative derivative majorant. -/
def ckPositiveMajorant
    (c : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    (s : ℝ) : ℝ := ∑' n, ‖c n‖ * (n + 1) * s ^ n

theorem ckPositiveMajorant_nonneg
    (c : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ ckPositiveMajorant c s := by
  exact tsum_nonneg (fun n => by positivity)

variable [CompleteSpace B]

/-- Absolute coefficient control supplies actual summability in the Banach target. -/
theorem ckPositiveMultilinearSum_summable
    (c : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c n‖ * (n + 1) * s ^ n))
    {x : H} (hx : ‖x‖ ≤ s) : Summable (fun n => c n (fun _ => x)) := by
  exact (hc.mul_right ‖x‖).of_norm_bounded
    (fun n => ck_multilinear_diagonal_norm_bound n (c n) hs hx)

/-- Quantitative norm bound for the actual superposition sum. -/
theorem ckPositiveMultilinearSum_norm_le
    (c : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c n‖ * (n + 1) * s ^ n))
    {x : H} (hx : ‖x‖ ≤ s) :
    ‖ckPositiveMultilinearSum c x‖ ≤ ckPositiveMajorant c s * ‖x‖ := by
  exact tsum_of_norm_bounded (hc.hasSum.mul_right ‖x‖)
    (fun n => ck_multilinear_diagonal_norm_bound n (c n) hs hx)

/-- Quantitative Lipschitz bound for the actual superposition sum. -/
theorem ckPositiveMultilinearSum_difference_le
    (c : ∀ n : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c n‖ * (n + 1) * s ^ n))
    {x y : H} (hx : ‖x‖ ≤ s) (hy : ‖y‖ ≤ s) :
    ‖ckPositiveMultilinearSum c x - ckPositiveMultilinearSum c y‖ ≤
      ckPositiveMajorant c s * ‖x - y‖ := by
  have hcx := ckPositiveMultilinearSum_summable c hs hc hx
  have hcy := ckPositiveMultilinearSum_summable c hs hc hy
  unfold ckPositiveMultilinearSum
  rw [← hcx.tsum_sub hcy]
  exact tsum_of_norm_bounded (hc.hasSum.mul_right ‖x - y‖)
    (fun n => ck_multilinear_diagonal_difference_bound n (c n) hs hx hy)

/-- Halving a positive convergence radius produces a summable derivative
majorant, without assuming a derivative-series convergence theorem. -/
theorem ck_summable_derivative_majorant_halfRadius
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {R : ℝ} (hR : 0 < R)
    (hseries : Summable (fun n => a n * R ^ n)) :
    Summable (fun n => a (n + 1) * (n + 1) * (R / 2) ^ n) := by
  have hshift : Summable (fun n => a (n + 1) * R ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 hseries
  apply Summable.of_nonneg_of_le
    (fun n => by have han := ha (n + 1); positivity) _ (hshift.mul_left (1 / R))
  intro n
  have han := ha (n + 1)
  have hdegree : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast n.lt_two_pow_self.succ_le
  calc
    a (n + 1) * (n + 1) * (R / 2) ^ n ≤
      a (n + 1) * (2 : ℝ) ^ n * (R / 2) ^ n := by
        gcongr
    _ = (1 / R) * (a (n + 1) * R ^ (n + 1)) := by
      rw [div_pow, pow_succ]
      field_simp [hR.ne'] <;> ring

end

end NSEGR.NativeLiterature
