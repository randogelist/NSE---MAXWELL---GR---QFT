import QuantumAdapter.Obligations.VariationalBounds
import QuantumAdapter.Obligations.LinearODE
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open Set Filter Metric
open scoped Topology ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

/-- Left composition by the actual derivative along an actual native orbit. -/
def phaseFlowVariationalOperator {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (q : Phase N)
    (t : ℝ) : (Phase N →L[ℝ] Phase N) →L[ℝ] (Phase N →L[ℝ] Phase N) :=
  ContinuousLinearMap.compL ℝ (Phase N) (Phase N) (Phase N)
    (fderiv ℝ (drift ν N) (F.map N t q))

theorem continuous_phaseFlowVariationalOperator {ν : ℝ}
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    Continuous (phaseFlowVariationalOperator F N q) :=
  (ContinuousLinearMap.compL ℝ (Phase N) (Phase N) (Phase N)).continuous.comp
    (continuous_native_variational_coefficient F N q)

/-- The variational fundamental matrix is an actual complete linear-ODE solution. -/
theorem exists_phaseFlowVariational {ν : ℝ}
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    ∃ J : ℝ → Phase N →L[ℝ] Phase N,
      J 0 = ContinuousLinearMap.id ℝ (Phase N) ∧ ∀ t,
      HasDerivAt J
        ((fderiv ℝ (drift ν N) (F.map N t q)).comp (J t)) t := by
  obtain ⟨J, hzero, hJ⟩ := exists_complete_linear_ode
    (phaseFlowVariationalOperator F N q)
    (continuous_phaseFlowVariationalOperator F N q)
    (ContinuousLinearMap.id ℝ (Phase N))
  exact ⟨J, hzero, fun t => by
    simpa only [phaseFlowVariationalOperator, ContinuousLinearMap.compL_apply] using hJ t⟩

def phaseFlowVariational {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    ℝ → Phase N →L[ℝ] Phase N :=
  Classical.choose (exists_phaseFlowVariational F N q)

theorem phaseFlowVariational_zero {ν : ℝ}
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    phaseFlowVariational F N q 0 = ContinuousLinearMap.id ℝ (Phase N) :=
  (Classical.choose_spec (exists_phaseFlowVariational F N q)).1

theorem phaseFlowVariational_hasDerivAt {ν : ℝ}
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) (t : ℝ) :
    HasDerivAt (phaseFlowVariational F N q)
      ((fderiv ℝ (drift ν N) (F.map N t q)).comp (phaseFlowVariational F N q t)) t :=
  (Classical.choose_spec (exists_phaseFlowVariational F N q)).2 t

/-- Exact signed-time initial-data derivative of the actual native flow. -/
theorem phaseFlow_timeMap_hasFDerivAt {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) (q : Phase N) :
    HasFDerivAt (F.map N t) (phaseFlowVariational F N q t) q := by
  let σ : ℝ := if 0 ≤ t then 1 else -1
  let T : ℝ := |t|
  let R₀ : ℝ := ‖q‖ + 1
  let R : ℝ := Real.sqrt (Real.exp ((2 * ν * finiteLaplaceTrace N) * T) * R₀ ^ 2)
  let b : Phase N → Phase N := fun z => σ • drift ν N z
  let Φ : ℝ → Phase N → Phase N := fun s z => F.map N (σ * s) z
  let J : ℝ → Phase N →L[ℝ] Phase N := fun s => phaseFlowVariational F N q (σ * s)
  have hσ : |σ| = 1 := by
    by_cases ht : 0 ≤ t <;> simp [σ, ht]
  have hσt : σ * T = t := by
    by_cases ht : 0 ≤ t
    · simp [σ, T, ht, abs_of_nonneg ht]
    · simp [σ, T, ht, abs_of_neg (lt_of_not_ge ht)]
  have hb : ContDiff ℝ ∞ b := (Assembly.contDiff_drift ν N).const_smul σ
  have hzero (z : Phase N) : Φ 0 z = z := by simp [Φ, F.map_zero]
  have hΦ (z : Phase N) (s : ℝ) :
      HasDerivAt (fun r => Φ r z) (b (Φ s z)) s := by
    simpa only [Φ, b, Function.comp_def] using
      (F.orbit_derivative N z (σ * s)).scomp s (hasDerivAt_const_mul σ)
  have hJzero : J 0 = ContinuousLinearMap.id ℝ (Phase N) := by
    simp only [J, mul_zero, phaseFlowVariational_zero]
  have hJ (s : ℝ) : HasDerivAt J ((fderiv ℝ b (Φ s q)).comp (J s)) s := by
    have hd := (phaseFlowVariational_hasDerivAt F N q (σ * s)).scomp s
      (hasDerivAt_const_mul σ)
    have hdb : fderiv ℝ b (Φ s q) =
        σ • fderiv ℝ (drift ν N) (Φ s q) :=
      (((Assembly.contDiff_drift ν N).differentiable (by simp) (Φ s q)).hasFDerivAt.const_smul σ).fderiv
    rw [hdb]
    simpa only [J, Φ, Function.comp_def, ContinuousLinearMap.smul_comp] using hd
  have htube (y : Phase N) (hy : y ∈ closedBall q 1)
      (s : ℝ) (hs : s ∈ Icc 0 T) : Φ s y ∈ closedBall (0 : Phase N) R := by
    have hdiff : ‖y - q‖ ≤ (1 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hy
    have hy0 : y ∈ closedBall (0 : Phase N) R₀ := by
      simp only [mem_closedBall, dist_zero_right]
      calc
        ‖y‖ = ‖(y - q) + q‖ := by congr 1; abel
        _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
        _ ≤ R₀ := by dsimp [R₀]; linarith
    have htime : |σ * s| ≤ T := by
      rw [abs_mul, hσ, one_mul, abs_of_nonneg hs.1]
      exact hs.2
    exact phaseFlow_uniform_orbit_ball hν F N (by dsimp [R₀]; positivity)
      (abs_nonneg t) hy0 htime
  have h := flow_hasFDerivAt_of_variational_on_bounded_tube b hb Φ hzero hΦ q
    (abs_nonneg t) htube J hJzero hJ
  simpa only [Φ, J, hσt] using h

/-- P2: all actual native time maps are differentiable, including negative times. -/
theorem phaseFlow_timeMap_differentiable {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) : Differentiable ℝ (F.map N t) :=
  fun q => (phaseFlow_timeMap_hasFDerivAt hν F N t q).differentiableAt

/-- The totalized derivative equals the constructed fundamental matrix. -/
theorem fderiv_phaseFlow_timeMap {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) (q : Phase N) :
    fderiv ℝ (F.map N t) q = phaseFlowVariational F N q t :=
  (phaseFlow_timeMap_hasFDerivAt hν F N t q).fderiv

/-- The precise variational ODE consumed by the determinant closure. -/
theorem phaseFlow_fderiv_hasDerivAt {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q : Phase N) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ (F.map N s) q)
      ((fderiv ℝ (drift ν N) (F.map N t q)).comp
        (fderiv ℝ (F.map N t) q)) t := by
  simp only [fderiv_phaseFlow_timeMap hν F N]
  exact phaseFlowVariational_hasDerivAt F N q t

end
end QuantumAdapter.Obligations
