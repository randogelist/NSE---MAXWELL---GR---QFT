import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Real factorial derivative bounds imply an actual convergent multilinear
Taylor series. No analyticity hypothesis occurs on the function. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1200000

namespace NSEGR.Assembly
open Set Filter Metric
open scoped Topology BigOperators ContDiff
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem factorialTaylor_remainder_bound (f : E → F) (x y : E)
    {r M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hy : ‖y‖ < r)
    (hf : ContDiffOn ℝ ∞ f (ball x r))
    (hbound : ∀ n z, z ∈ ball x r →
      ‖iteratedFDeriv ℝ n f z‖ ≤ M * A ^ n * (n.factorial : ℝ)) (n : ℕ) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖ ≤
        M * (n + 1 : ℝ) * (A * ‖y‖) ^ (n + 1) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • y ∈ ball x r := by
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1] using
      (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans_lt hy
  have hcd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ (n + 1) f (x + t • y) :=
    ((hf _ (hmem t ht)).contDiffAt (isOpen_ball.mem_nhds (hmem t ht))).of_le (by simp)
  have heq := map_add_eq_sum_add_integral_iteratedFDeriv hcd
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hfacnonneg : 0 ≤ (n.factorial : ℝ)⁻¹ := by positivity
  let C : ℝ := M * A ^ (n + 1) * ((n + 1).factorial : ℝ) * ‖y‖ ^ (n + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ C := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C) (f := fun t =>
        (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y))
    apply (by simpa using hb :
      (∀ t ∈ Ioc (0 : ℝ) 1, ‖(1 - t)^n •
        iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ C) → _)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hpow : |(1 - t)^n| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) n)]
      exact pow_le_one₀ (sub_nonneg.mpr ht.2) (by linarith)
    have hmap : ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ C := by
      calc
        _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ‖y‖ ^ (n + 1) := by
          simpa using (iteratedFDeriv ℝ (n + 1) f (x + t • y)).le_opNorm (fun _ => y)
        _ ≤ C := mul_le_mul_of_nonneg_right (hbound (n + 1) _ (hmem t ht'))
          (pow_nonneg (norm_nonneg y) _)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hpow hmap (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  have hrem : f (x + y) - ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y) =
      (n.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
        (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y) :=
    sub_eq_iff_eq_add.mpr (by simpa [add_comm] using heq)
  rw [hrem, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfacnonneg]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left hint hfacnonneg
    _ = M * (n + 1 : ℝ) * (A * ‖y‖) ^ (n + 1) := by
      dsimp [C]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
      field_simp

theorem analyticAt_of_iteratedFDeriv_bound (f : E → F) (x : E)
    {r M A : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hf : ContDiffOn ℝ ∞ f (ball x r))
    (hbound : ∀ n z, z ∈ ball x r →
      ‖iteratedFDeriv ℝ n f z‖ ≤ M * A ^ n * (n.factorial : ℝ)) :
    AnalyticAt ℝ f x := by
  let p : FormalMultilinearSeries ℝ E F :=
    fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f x
  have hcoef (n : ℕ) : ‖p n‖ ≤ M * A ^ n := by
    have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hfacpos : 0 ≤ (n.factorial : ℝ)⁻¹ := by positivity
    calc
      ‖p n‖ = (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n f x‖ := by
        simp [p, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfacpos]
      _ ≤ (n.factorial : ℝ)⁻¹ * (M * A ^ n * (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound n x (mem_ball_self hr)) hfacpos
      _ = M * A ^ n := by field_simp
  let R : ℝ := min r (1 / (2 * A + 1))
  have hden : 0 < 2 * A + 1 := by positivity
  have hR : 0 < R := lt_min hr (one_div_pos.mpr hden)
  have hRr : R ≤ r := min_le_left _ _
  have hRA : R * (2 * A + 1) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hAR : A * R ≤ 1 := by nlinarith
  let ρ : ℝ≥0 := ⟨R, hR.le⟩
  have hrad : (ρ : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound M
    intro n
    calc
      ‖p n‖ * (ρ : ℝ) ^ n ≤ (M * A ^ n) * R ^ n :=
        mul_le_mul_of_nonneg_right (hcoef n) (pow_nonneg hR.le _)
      _ = M * (A * R) ^ n := by rw [mul_pow]; ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (mul_nonneg hA hR.le) hAR) hM
      _ = M := mul_one M
  refine ⟨p, (ρ : ℝ≥0∞), hrad, ?_, ?_⟩
  · exact_mod_cast hR
  · intro y hy
    have hyR : ‖y‖ < R := by simpa [Metric.eball_coe, mem_ball, dist_zero_right, ρ] using hy
    have hyr : ‖y‖ < r := hyR.trans_le hRr
    have hyden : ‖y‖ * (2 * A + 1) < 1 :=
      (mul_lt_mul_of_pos_right hyR hden).trans_le hRA
    have hq : 0 ≤ 2 * (A * ‖y‖) := by positivity
    have hq1 : 2 * (A * ‖y‖) < 1 := by nlinarith [norm_nonneg y]
    have hsum := p.summable_norm_apply (Metric.eball_subset_eball hrad hy)
    apply (hasSum_iff_tendsto_nat_of_summable_norm hsum).mpr
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
    have hlim : Tendsto (fun n : ℕ => M * (2 * (A * ‖y‖)) ^ (n + 1))
        atTop (𝓝 0) := by simpa only [pow_succ, mul_zero, zero_mul] using
          (hp.mul_const (2 * (A * ‖y‖))).const_mul M
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have hn : (n + 1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self (n + 1)).le
    calc
      ‖(∑ k ∈ Finset.range (n + 1), p k (fun _ => y)) - f (x + y)‖
          = ‖f (x + y) - ∑ k ∈ Finset.range (n + 1),
            (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖ := by
              simp only [p, ContinuousMultilinearMap.smul_apply, norm_sub_rev]
      _ ≤ M * (n + 1 : ℝ) * (A * ‖y‖) ^ (n + 1) :=
        factorialTaylor_remainder_bound f x y hM hA hyr hf hbound n
      _ ≤ M * (2 : ℝ) ^ (n + 1) * (A * ‖y‖) ^ (n + 1) := by gcongr
      _ = M * (2 * (A * ‖y‖)) ^ (n + 1) := by rw [mul_pow]; ring

end
end NSEGR.Assembly
