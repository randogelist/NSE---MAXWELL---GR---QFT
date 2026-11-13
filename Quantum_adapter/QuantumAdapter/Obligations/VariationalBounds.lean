import QuantumAdapter.Obligations.Variational
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped Topology ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz derivative gives a quadratic Taylor remainder on a convex set. -/
theorem quadratic_remainder_of_lipschitz_fderiv
    (b : E → E) {S : Set E} (hS : Convex ℝ S)
    (hb : Differentiable ℝ b) {K : ℝ≥0}
    (hK : LipschitzOnWith K (fderiv ℝ b) S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖b y - b x - fderiv ℝ b x (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hbound (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ b z - fderiv ℝ b x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    have h := hK.dist_le_mul z (hseg hz) x hx
    have h' : ‖fderiv ℝ b z - fderiv ℝ b x‖ ≤ (K : ℝ) * ‖z - x‖ := by
      simpa only [dist_eq_norm] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hb z) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using h

/-- Native smooth finite-dimensional vector fields have uniform quadratic remainders on balls. -/
theorem smooth_quadratic_remainder_on_closedBall [ProperSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall (0 : E) R,
      ∀ y ∈ closedBall (0 : E) R,
      ‖b y - b x - fderiv ℝ b x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hdb : ContDiff ℝ ∞ (fderiv ℝ b) := (contDiff_infty_iff_fderiv.mp hb).2
  obtain ⟨K, hK⟩ := hdb.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x hx y hy
  exact quadratic_remainder_of_lipschitz_fderiv b (convex_closedBall (0 : E) R)
    (hb.differentiable (by simp)) hK hx hy

/-- A bounded orbit tube and the actual variational ODE imply initial-data differentiability. -/
theorem flow_hasFDerivAt_of_variational_on_bounded_tube [ProperSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (Φ : ℝ → E → E) (hzero : ∀ z, Φ 0 z = z)
    (hΦ : ∀ z s, HasDerivAt (fun t => Φ t z) (b (Φ s z)) s)
    (x : E) {T R : ℝ} (hT : 0 ≤ T)
    (htube : ∀ y ∈ closedBall x 1, ∀ s ∈ Icc 0 T, Φ s y ∈ closedBall (0 : E) R)
    (J : ℝ → E →L[ℝ] E) (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hJ : ∀ s, HasDerivAt J ((fderiv ℝ b (Φ s x)).comp (J s)) s) :
    HasFDerivAt (Φ T) (J T) x := by
  obtain ⟨K, hK⟩ := hb.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  obtain ⟨C, hC, hquad⟩ := smooth_quadratic_remainder_on_closedBall b hb R
  have hAc : Continuous (fun s => fderiv ℝ b (Φ s x)) :=
    (hb.continuous_fderiv (by simp)).comp
      (continuous_iff_continuousAt.mpr (fun s => (hΦ x s).continuousAt))
  obtain ⟨KA, hKA⟩ := (isCompact_Icc : IsCompact (Icc 0 T)).exists_bound_of_continuousOn
    (f := fun s : ℝ => fderiv ℝ b (Φ s x)) hAc.continuousOn
  apply flow_hasFDerivAt_of_variational_remainder b Φ J
    (fun s => fderiv ℝ b (Φ s x)) x hT hC (Real.exp_nonneg ((K : ℝ) * T))
    hzero hJzero hΦ hJ hKA
  filter_upwards [ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with h hh
  have hy : x + h ∈ closedBall x 1 := by
    have hnorm : ‖h‖ ≤ (1 : ℝ) := by
      exact (show ‖h‖ < (1 : ℝ) by simpa only [mem_ball, dist_zero_right] using hh).le
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hnorm
  have hx : x ∈ closedBall x 1 := mem_closedBall_self (by norm_num)
  constructor
  · intro s hs
    have hd := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => b) (s := fun _ => closedBall (0 : E) R)
      (K := K) (a := 0) (b := T) (δ := ‖h‖)
      (fun _ _ => hK)
      ((continuous_iff_continuousAt.mpr (fun t => (hΦ (x + h) t).continuousAt)).continuousOn)
      (fun t _ => (hΦ (x + h) t).hasDerivWithinAt)
      (fun t ht => htube (x + h) hy t (Ico_subset_Icc_self ht))
      ((continuous_iff_continuousAt.mpr (fun t => (hΦ x t).continuousAt)).continuousOn)
      (fun t _ => (hΦ x t).hasDerivWithinAt)
      (fun t ht => htube x hx t (Ico_subset_Icc_self ht))
      (by simp only [hzero, dist_eq_norm, add_sub_cancel_left]; exact le_rfl) s hs
    have hd' : ‖Φ s (x + h) - Φ s x‖ ≤ ‖h‖ * Real.exp ((K : ℝ) * s) := by
      simpa only [dist_eq_norm, sub_zero] using hd
    calc
      _ ≤ ‖h‖ * Real.exp ((K : ℝ) * s) := hd'
      _ ≤ ‖h‖ * Real.exp ((K : ℝ) * T) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hs.2 K.coe_nonneg)) (norm_nonneg h)
      _ = Real.exp ((K : ℝ) * T) * ‖h‖ := mul_comm _ _
  · intro s hs
    exact hquad (Φ s x) (htube x hx s hs) (Φ s (x + h)) (htube (x + h) hy s hs)

/-- Every bounded initial phase ball stays bounded over a prescribed signed-time horizon. -/
theorem phaseFlow_uniform_orbit_ball {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    {q : Phase N} (hq : q ∈ closedBall (0 : Phase N) R)
    {t : ℝ} (ht : |t| ≤ T) :
    F.map N t q ∈ closedBall (0 : Phase N)
      (Real.sqrt (Real.exp ((2 * ν * finiteLaplaceTrace N) * T) * R ^ 2)) := by
  have hd : 0 ≤ 2 * ν * finiteLaplaceTrace N :=
    mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N)
  have hqnorm : ‖q‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hq
  have hq2 : energy0 N q ≤ R ^ 2 := by
    rw [Assembly.energy0_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg q) hR).2 hqnorm
  have he : energy0 N (F.map N t q) ≤
      Real.exp ((2 * ν * finiteLaplaceTrace N) * T) * R ^ 2 := by
    apply (Assembly.phaseFlow_energy0_bound_abs hν F N q t).trans
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hd)) (energy0_nonneg N q)).trans
      (mul_le_mul_of_nonneg_left hq2 (Real.exp_nonneg _))
  have hn := Real.sqrt_le_sqrt he
  simpa only [mem_closedBall, dist_zero_right, Assembly.energy0_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg (F.map N t q))] using hn

end
end QuantumAdapter.Obligations
