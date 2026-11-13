import QuantumAdapter.Assembly.Flow
import QuantumAdapter.Assembly.Fourier
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Joint continuity from the actual finite energy bound

Only continuity of each fixed-time map is an explicit parameter hypothesis.
Uniform time control follows from the native energy identity and finite-
dimensional boundedness of the actual drift. This supplies product
measurability for subsequent packet integrals.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped BigOperators ContDiff Topology NNReal

namespace QuantumAdapter.Assembly

noncomputable section

/-- The same energy majorant holds for all signed times of absolute value at most one. -/
theorem phaseFlow_energy0_bound_unit {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) {t : ℝ} (ht : |t| ≤ 1) :
    energy0 N (F.map N t q) ≤
      Real.exp (2 * ν * finiteLaplaceTrace N) * energy0 N q := by
  have hd : 0 ≤ 2 * ν * finiteLaplaceTrace N :=
    mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N)
  rcases le_total 0 t with ht0 | ht0
  · apply (phaseFlow_energy0_le_initial hν F N q ht0).trans
    have he : 1 ≤ Real.exp (2 * ν * finiteLaplaceTrace N) :=
      Real.one_le_exp_iff.mpr hd
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right he (energy0_nonneg N q)
  · apply (phaseFlow_energy0_backward_bound hν F N q ht0).trans
    apply mul_le_mul_of_nonneg_right _ (energy0_nonneg N q)
    apply Real.exp_le_exp.mpr
    have hlow : -1 ≤ t := (abs_le.mp ht).1
    nlinarith

/-- A uniform time-Lipschitz constant for all initial phases in a bounded ball. -/
theorem phaseFlow_uniform_time_lipschitz {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ q : Phase N, ‖q‖ ≤ R →
      LipschitzOnWith C (fun t => F.map N t q) (Ioo (-1 : ℝ) 1) := by
  let M : ℝ := Real.sqrt (Real.exp (2 * ν * finiteLaplaceTrace N) * R ^ 2)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Phase N) M).exists_bound_of_continuousOn
    (contDiff_drift ν N).continuous.continuousOn
  let C : ℝ≥0 := ⟨max B 0, le_max_right B 0⟩
  refine ⟨C, ?_⟩
  intro q hq
  apply (convex_Ioo (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.orbit_derivative N q t).hasDerivWithinAt)
  intro t ht
  have ht' : |t| ≤ 1 := (abs_lt.mpr ht).le
  have hE := phaseFlow_energy0_bound_unit hν F N q ht'
  have hq2 : energy0 N q ≤ R ^ 2 := by
    rw [energy0_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg q) hR).2 hq
  have hE' : energy0 N (F.map N t q) ≤
      Real.exp (2 * ν * finiteLaplaceTrace N) * R ^ 2 :=
    hE.trans (mul_le_mul_of_nonneg_left hq2 (Real.exp_nonneg _))
  have hnorm : ‖F.map N t q‖ ≤ M := by
    have hs := Real.sqrt_le_sqrt hE'
    simpa only [energy0_eq_norm_sq, Real.sqrt_sq (norm_nonneg (F.map N t q))] using hs
  have hmem : F.map N t q ∈ closedBall (0 : Phase N) M := by
    simpa only [mem_closedBall, dist_zero_right] using hnorm
  have hb : ‖drift ν N (F.map N t q)‖ ≤ max B 0 :=
    (hB _ hmem).trans (le_max_left B 0)
  exact_mod_cast hb

/-- Small time displacement is uniform on bounded initial phases. -/
theorem phaseFlow_small_time_dist {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    {R : ℝ} {C : ℝ≥0}
    (hC : ∀ q : Phase N, ‖q‖ ≤ R →
      LipschitzOnWith C (fun t => F.map N t q) (Ioo (-1 : ℝ) 1))
    {q : Phase N} (hq : ‖q‖ ≤ R) {t : ℝ} (ht : |t| < 1) :
    dist (F.map N t q) q ≤ (C : ℝ) * |t| := by
  have h := (hC q hq).dist_le_mul t (abs_lt.mp ht) 0 (by norm_num)
  simpa only [F.map_zero, Real.dist_eq, sub_zero] using h

set_option maxHeartbeats 800000 in
/-- Fixed-time continuity plus native uniform energy control implies joint continuity. -/
theorem continuous_phaseFlow_uncurry_of_timeMaps {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ)
    (hc : ∀ t : ℝ, Continuous (F.map N t)) :
    Continuous (fun p : ℝ × Phase N => F.map N p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨C, hC⟩ := phaseFlow_uniform_time_lipschitz hν F N
    (R := ‖p₀.2‖ + 1) (by positivity)
  have hs : Tendsto (fun p : ℝ × Phase N => F.map N (p.1 - p₀.1) p.2)
      (𝓝 p₀) (𝓝 p₀.2) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have htime : Tendsto (fun p : ℝ × Phase N => dist p.1 p₀.1)
        (𝓝 p₀) (𝓝 0) := by
      have hcont : Continuous (fun p : ℝ × Phase N => dist p.1 p₀.1) := by fun_prop
      simpa only [dist_self] using hcont.tendsto p₀
    have hspace : Tendsto (fun p : ℝ × Phase N => dist p.2 p₀.2)
        (𝓝 p₀) (𝓝 0) := by
      have hcont : Continuous (fun p : ℝ × Phase N => dist p.2 p₀.2) := by fun_prop
      simpa only [dist_self] using hcont.tendsto p₀
    have htotal : Tendsto (fun p : ℝ × Phase N =>
        (C : ℝ) * dist p.1 p₀.1 + dist p.2 p₀.2) (𝓝 p₀) (𝓝 0) := by
      simpa only [mul_zero, zero_add] using (htime.const_mul (C : ℝ)).add hspace
    filter_upwards [(tendsto_order.mp htime).2 1 zero_lt_one,
      (tendsto_order.mp hspace).2 1 zero_lt_one,
      (tendsto_order.mp htotal).2 ε hε] with p hpt hpq hpε
    have hpbound : ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
      have hnorm := norm_le_norm_sub_add p.2 p₀.2
      rw [← dist_eq_norm] at hnorm
      exact hnorm.trans (by simpa only [add_comm] using add_le_add_right hpq.le ‖p₀.2‖)
    have hpt' : |p.1 - p₀.1| < 1 := by simpa only [Real.dist_eq] using hpt
    have hsmall : dist (F.map N (p.1 - p₀.1) p.2) p.2 ≤
        (C : ℝ) * |p.1 - p₀.1| :=
      phaseFlow_small_time_dist F N hC hpbound hpt'
    calc
      dist (F.map N (p.1 - p₀.1) p.2) p₀.2
          ≤ dist (F.map N (p.1 - p₀.1) p.2) p.2 + dist p.2 p₀.2 :=
            dist_triangle _ _ _
      _ ≤ (C : ℝ) * |p.1 - p₀.1| + dist p.2 p₀.2 := add_le_add_right hsmall _
      _ < ε := by simpa only [Real.dist_eq] using hpε
  have hout := (hc p₀.1).continuousAt.tendsto.comp hs
  have heq : (fun p : ℝ × Phase N => F.map N p.1 p.2) =
      (fun p : ℝ × Phase N => F.map N p₀.1 (F.map N (p.1 - p₀.1) p.2)) := by
    funext p
    rw [← F.map_add]
    congr 1
    ring
  change Tendsto (fun p : ℝ × Phase N => F.map N p.1 p.2)
    (𝓝 p₀) (𝓝 (F.map N p₀.1 p₀.2))
  rw [heq]
  exact hout

/-- Differentiability of every time map suffices for the actual product continuity. -/
theorem continuous_phaseFlow_uncurry_of_differentiable {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ)
    (hd : ∀ t : ℝ, Differentiable ℝ (F.map N t)) :
    Continuous (fun p : ℝ × Phase N => F.map N p.1 p.2) :=
  continuous_phaseFlow_uncurry_of_timeMaps hν F N (fun t => (hd t).continuous)

/-- The native phase-time map is measurable under the same explicit hypothesis. -/
theorem measurable_phaseFlow_uncurry_of_differentiable {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ)
    (hd : ∀ t : ℝ, Differentiable ℝ (F.map N t)) :
    Measurable (fun p : ℝ × Phase N => F.map N p.1 p.2) :=
  (continuous_phaseFlow_uncurry_of_differentiable hν F N hd).measurable

end

end QuantumAdapter.Assembly

