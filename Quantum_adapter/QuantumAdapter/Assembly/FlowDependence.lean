import QuantumAdapter.Assembly.FlowContinuity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped BigOperators ContDiff Topology NNReal

namespace QuantumAdapter.Assembly

noncomputable section

/-- Native energy control at arbitrary signed times. -/
theorem phaseFlow_energy0_bound_abs {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) (t : ℝ) :
    energy0 N (F.map N t q) ≤
      Real.exp ((2 * ν * finiteLaplaceTrace N) * |t|) * energy0 N q := by
  rcases le_total 0 t with ht | ht
  · apply (phaseFlow_energy0_le_initial hν F N q ht).trans
    have he : 1 ≤ Real.exp ((2 * ν * finiteLaplaceTrace N) * |t|) :=
      Real.one_le_exp_iff.mpr (by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N))
          (abs_nonneg t))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (energy0_nonneg N q)
  · have h := phaseFlow_energy0_backward_bound hν F N q ht
    simpa only [abs_of_nonpos ht, mul_neg] using h

/-- Native complete time maps are Lipschitz on each bounded initial phase ball. -/
theorem phaseFlow_timeMap_lipschitzOn_closedBall {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ L : ℝ≥0, LipschitzOnWith L (F.map N t) (closedBall (0 : Phase N) R) := by
  let σ : ℝ := if 0 ≤ t then 1 else -1
  let d : ℝ := 2 * ν * finiteLaplaceTrace N
  let M : ℝ := Real.sqrt (Real.exp (d * |t|) * R ^ 2)
  have hd : 0 ≤ d :=
    mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N)
  have hσ : |σ| = 1 := by
    by_cases ht : 0 ≤ t <;> simp [σ, ht]
  have hσt : σ * |t| = t := by
    by_cases ht : 0 ≤ t
    · simp [σ, ht, abs_of_nonneg ht]
    · simp [σ, ht, abs_of_neg (lt_of_not_ge ht)]
  have hw : ContDiff ℝ 1 (fun x : Phase N => σ • drift ν N x) :=
    ((contDiff_drift ν N).of_le (by simp)).const_smul σ
  obtain ⟨K, hK⟩ := hw.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : Phase N) M) (isCompact_closedBall (0 : Phase N) M)
  have hbound (q : Phase N) (hq : q ∈ closedBall (0 : Phase N) R)
      (s : ℝ) (hs : s ∈ Icc 0 |t|) :
      F.map N (σ * s) q ∈ closedBall (0 : Phase N) M := by
    have hqnorm : ‖q‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hq
    have hq2 : energy0 N q ≤ R ^ 2 := by
      rw [energy0_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg q) hR).2 hqnorm
    have htime : |σ * s| ≤ |t| := by
      rw [abs_mul, hσ, one_mul, abs_of_nonneg hs.1]
      exact hs.2
    have he : Real.exp (d * |σ * s|) ≤ Real.exp (d * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hd)
    have hE : energy0 N (F.map N (σ * s) q) ≤ Real.exp (d * |t|) * R ^ 2 :=
      (phaseFlow_energy0_bound_abs hν F N q (σ * s)).trans
        ((mul_le_mul_of_nonneg_right he (energy0_nonneg N q)).trans
          (mul_le_mul_of_nonneg_left hq2 (Real.exp_nonneg _)))
    have hnorm : ‖F.map N (σ * s) q‖ ≤ M := by
      have hsqrt := Real.sqrt_le_sqrt hE
      simpa only [energy0_eq_norm_sq,
        Real.sqrt_sq (norm_nonneg (F.map N (σ * s) q))] using hsqrt
    simpa only [mem_closedBall, dist_zero_right] using hnorm
  have hderiv (q : Phase N) (s : ℝ) :
      HasDerivAt (fun u => F.map N (σ * u) q)
        (σ • drift ν N (F.map N (σ * s) q)) s := by
    simpa only [Function.comp_def] using
      (F.orbit_derivative N q (σ * s)).scomp s (hasDerivAt_const_mul σ)
  refine ⟨⟨Real.exp ((K : ℝ) * |t|), Real.exp_nonneg _⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (F.map N t x) (F.map N t y) ≤
    Real.exp ((K : ℝ) * |t|) * dist x y
  have h := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ (z : Phase N) => σ • drift ν N z)
    (s := fun _ => closedBall (0 : Phase N) M)
    (K := K) (a := 0) (b := |t|) (δ := dist x y)
    (fun _ _ => hK)
    ((continuous_iff_continuousAt.mpr (fun s => (hderiv x s).continuousAt)).continuousOn)
    (fun s _ => (hderiv x s).hasDerivWithinAt)
    (fun s hs => hbound x hx s (Ico_subset_Icc_self hs))
    ((continuous_iff_continuousAt.mpr (fun s => (hderiv y s).continuousAt)).continuousOn)
    (fun s _ => (hderiv y s).hasDerivWithinAt)
    (fun s hs => hbound y hy s (Ico_subset_Icc_self hs))
    (by simp only [mul_zero, F.map_zero]; exact le_rfl) |t| ⟨abs_nonneg t, le_rfl⟩
  simpa only [hσt, sub_zero, mul_comm] using h

/-- Initial-data continuity follows from the actual drift and energy bounds. -/
theorem continuous_phaseFlow_timeMap {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) : Continuous (F.map N t) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨L, hL⟩ := phaseFlow_timeMap_lipschitzOn_closedBall hν F N t
    (R := ‖q‖ + 1) (by positivity)
  apply hL.continuousOn.continuousAt
  apply mem_of_superset (isOpen_ball.mem_nhds (show q ∈ ball (0 : Phase N) (‖q‖ + 1) by
    simp only [mem_ball, dist_zero_right]
    linarith))
  exact ball_subset_closedBall

/-- Native complete phase flows are jointly continuous without a regularity certificate. -/
theorem continuous_phaseFlow_uncurry {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) :
    Continuous (fun p : ℝ × Phase N => F.map N p.1 p.2) :=
  continuous_phaseFlow_uncurry_of_timeMaps hν F N (continuous_phaseFlow_timeMap hν F N)

/-- Native complete phase flows are product-measurable without a regularity certificate. -/
theorem measurable_phaseFlow_uncurry {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) :
    Measurable (fun p : ℝ × Phase N => F.map N p.1 p.2) :=
  (continuous_phaseFlow_uncurry hν F N).measurable

end

end QuantumAdapter.Assembly
