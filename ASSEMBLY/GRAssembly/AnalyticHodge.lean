import GRAssembly.HodgeCommutation
import GRAssembly.AnalyticHodgeInput
import GRAssembly.AnalyticHodgeCalculus
import GRAssembly.AnalyticHodgeTaylor

/-!
Joint real analytic preservation by the actual mean-zero Poisson inverse
and actual Leray projection, on exactly the original open time slab.
The proof combines a fixed order-eight smooth estimate with uniform real
analytic input bounds, absorbs the fixed factorial shift, and identifies
the native multilinear Taylor series through its remainder estimate.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly

open Set Metric
open scoped BigOperators ContDiff Topology

noncomputable section

theorem poissonInverse_iteratedFDeriv_bound_eight
    (f : Pressure) {I : Set ℝ} (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t)) {t : ℝ} (ht : t ∈ I)
    {M A : ℝ} (hM : 0 ≤ M) (hA : 1 ≤ A)
    (hb : ∀ (k : ℕ) (y : Vec), y ∈ unitCube →
      ‖iteratedFDeriv ℝ k (fun z : ℝ × Vec => f z.1 z.2) (t, y)‖ ≤
        M * A ^ k * (k.factorial : ℝ)) (n : ℕ) (x : Vec) :
    ‖iteratedFDeriv ℝ n
      (fun z : ℝ × Vec => poissonInverse (f z.1) z.2) (t, x)‖ ≤
        poissonInverseFixedLossConstant * M * A ^ (n + 8) *
          ((n + 8).factorial : ℝ) := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hC0 := poissonInverseFixedLossConstant_pos.le
  let B : ℝ := M * A ^ (n + 8) * ((n + 8).factorial : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hv : 0 ≤ ∏ i : Fin n, ‖v i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  obtain ⟨hvs, hvp⟩ := iteratedFDeriv_slice_smooth_periodic f hI hf hp ht n v
  have hzero : ∀ y ∈ unitCube,
      ‖iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, y) v‖ ≤
        B * ∏ i : Fin n, ‖v i‖ := by
    intro y hy
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, y)‖ *
          ∏ i : Fin n, ‖v i‖ :=
        (iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, y)).le_opNorm v
      _ ≤ (M * A ^ n * (n.factorial : ℝ)) * ∏ i : Fin n, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (hb n y hy) hv
      _ ≤ B * ∏ i : Fin n, ‖v i‖ := by
        apply mul_le_mul_of_nonneg_right _ hv
        simpa only [B, mul_assoc] using
          mul_le_mul_of_nonneg_left (analyticHodge_order_monotone hA n 8) hM
  have height : ∀ j : Fin 3, ∀ y ∈ unitCube,
      ‖scalarSpatialIterate j 8
        (fun q => iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (t, q) v) y‖ ≤
          B * ∏ i : Fin n, ‖v i‖ := by
    intro j y hy
    rw [scalarSpatialIterate_iteratedFDeriv f hI hf hp ht n 8 v j]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n + 8) (fun z : ℝ × Vec => f z.1 z.2) (t, y)‖ *
          ∏ i : Fin (n + 8), ‖prependSpatialDirections j 8 v i‖ :=
        (iteratedFDeriv ℝ (n + 8) (fun z : ℝ × Vec => f z.1 z.2) (t, y)).le_opNorm
          (prependSpatialDirections j 8 v)
      _ ≤ B * ∏ i : Fin n, ‖v i‖ := by
        rw [prependSpatialDirections_norm_prod]
        exact mul_le_mul_of_nonneg_right (hb (n + 8) y hy) hv
  rw [poissonInverse_iteratedFDeriv_commute f hI hf hp ht n v x]
  calc
    _ ≤ poissonInverseFixedLossConstant * (B * ∏ i : Fin n, ‖v i‖) :=
      poissonInverse_norm_le_eight _ hvs hvp _ (mul_nonneg hB hv) hzero height x
    _ = (poissonInverseFixedLossConstant * M * A ^ (n + 8) *
          ((n + 8).factorial : ℝ)) * ∏ i : Fin n, ‖v i‖ := by
      dsimp [B]
      ring

/-- Actual Poisson inversion preserves joint real analyticity on the full
original open slab. All neighborhoods used in the proof are point-local. -/
theorem poissonInverse_joint_analytic_on_open_slab
    (f : Pressure) {I : Set ℝ} (hI : IsOpen I)
    (hf : AnalyticOnNhd ℝ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t)) :
    AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => poissonInverse (f z.1) z.2) {z | z.1 ∈ I} := by
  have hfs : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I} :=
    hf.contDiffOn_of_completeSpace
  have hGs := poissonInverse_joint_smooth_on_open_slab f hI hfs hp
  intro z hz
  obtain ⟨r, M, A, hr, hM, hA, hsub, hb⟩ :=
    analyticHodge_open_slab_local_uniform_bound f hI hf hz
  have htime (w : ℝ × Vec) (hw : w ∈ ball z r) : w.1 ∈ closedBall z.1 r := by
    rw [mem_closedBall, dist_eq_norm]
    have hw' : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    exact (norm_fst_le (w - z)).trans hw'.le
  let C : ℝ := poissonInverseFixedLossConstant * M * A ^ 8 *
    (Nat.factorial 8 : ℝ) * (2 : ℝ) ^ 8
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hC0 := poissonInverseFixedLossConstant_pos.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply analyticAt_of_iteratedFDeriv_bound
    (fun w : ℝ × Vec => poissonInverse (f w.1) w.2) z hr hC
    (show 0 ≤ 2 * A by positivity) (hGs.mono (fun w hw => hsub (htime w hw)))
  intro n w hw
  have hwI := hsub (htime w hw)
  have hraw := poissonInverse_iteratedFDeriv_bound_eight f hI hfs hp hwI hM.le hA
    (fun k y hy => hb k w.1 (htime w hw) y hy) n w.2
  exact hraw.trans (analyticHodge_absorb_fixed_loss hC0 hM.le hA0 n 8)

/-- Analyticity of the actual cube mean, on precisely the input interval. -/
theorem scalarMean_analytic_on_open_slab
    (f : Pressure) {I : Set ℝ} (hI : IsOpen I)
    (hf : AnalyticOnNhd ℝ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t)) :
    AnalyticOnNhd ℝ (fun t => scalarMean (f t)) I :=
  scalarMean_analytic_of_poissonInverse_analytic f hI hf hp
    (poissonInverse_joint_analytic_on_open_slab f hI hf hp)

/-- The exact Leray formula preserves joint analyticity and retains the
input time interval; no condition is imposed on the input constant mode. -/
theorem leray_joint_analytic_on_open_slab
    (w : Velocity) {I : Set ℝ} (hI : IsOpen I)
    (hw : AnalyticOnNhd ℝ (fun z : ℝ × Vec => w z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (w t)) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => leray (w z.1) z.2) {z | z.1 ∈ I} := by
  have hd : AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => divergence (w z.1) z.2) {z | z.1 ∈ I} :=
    fun z hz => analyticHodge_divergence_joint (hw z hz)
  have hdp : ∀ t ∈ I, SpatialPeriodic (divergence (w t)) :=
    fun t ht => divergence_periodic (hp t ht)
  have hG := poissonInverse_joint_analytic_on_open_slab
    (fun t => divergence (w t)) hI hd hdp
  intro z hz
  exact (hw z hz).sub (analyticHodge_gradient_joint
    (f := fun t => poissonInverse (divergence (w t))) (hG z hz))

end
end NSEGR.Assembly
