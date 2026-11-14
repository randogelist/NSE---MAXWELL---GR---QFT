import GRAssembly.Strengthening.AnalyticalFrontier.CheckpointFinal

/-!
Quantitative checkpoint immediately upstream of the exact factorial checkpoint.
The constants retain the time-Cauchy radius and positive spatial exponential
margin produced by the Wiener/Gevrey construction.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped Topology ContDiff

namespace NSEGR.Strengthening
noncomputable section

/--
At every positive spacetime point, the supplied trajectory has a smooth
neighborhood and the explicit mixed Cauchy/Gevrey bound

  R * (4 * max r⁻¹ σ⁻¹)^n * n!.

This is the exact quantitative endpoint expected from the fixed-margin
Wiener holomorphy stage.
-/
def ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : Field), NSEMaxwell.Classical.Data a →
      ∀ (s : NormalizedForwardTrajectory ν a) (z : ℝ × Vec),
        z ∈ positiveSpacetime →
          ∃ r σ R : ℝ,
            0 < r ∧
            0 < σ ∧
            0 ≤ R ∧
            ContDiffOn ℝ ∞
              (fun w : ℝ × Vec => s.totalVelocity w.1 w.2)
              (Metric.ball z r) ∧
            ∀ n w, w ∈ Metric.ball z r →
              ‖iteratedFDeriv ℝ n
                  (fun q : ℝ × Vec => s.totalVelocity q.1 q.2) w‖ ≤
                R * (4 * max r⁻¹ σ⁻¹) ^ n * (n.factorial : ℝ)

/-- The explicit Cauchy/Gevrey constants instantiate the generic factorial checkpoint. -/
theorem ANALYTICAL_FACTORIAL_CHECKPOINT_of_quantitative
    (checkpoint : ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT) :
    ANALYTICAL_FACTORIAL_CHECKPOINT := by
  intro ν hν a ha s z hz
  obtain ⟨r, σ, R, hr, hσ, hR, hsmooth, hbound⟩ :=
    checkpoint ν hν a ha s z hz
  refine ⟨r, R, 4 * max r⁻¹ σ⁻¹, hr, hR, ?_, hsmooth, ?_⟩
  · exact mul_nonneg (by norm_num)
      ((le_of_lt (inv_pos.mpr hr)).trans (le_max_left _ _))
  · intro n w hw
    exact hbound n w hw

/-- Quantitative checkpoint to the pointwise analytic checkpoint. -/
theorem ANALYTICAL_POINTWISE_CHECKPOINT_of_quantitative
    (checkpoint : ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT) :
    ANALYTICAL_POINTWISE_CHECKPOINT :=
  ANALYTICAL_POINTWISE_CHECKPOINT_of_factorial
    (ANALYTICAL_FACTORIAL_CHECKPOINT_of_quantitative checkpoint)

/-- Quantitative checkpoint to the exact universal positive-spacetime endpoint. -/
theorem ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT_of_quantitative
    (checkpoint : ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT) :
    ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT :=
  ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT_of_pointwise
    (ANALYTICAL_POINTWISE_CHECKPOINT_of_quantitative checkpoint)

/-- Quantitative checkpoint to the named analytic-selection frontier. -/
theorem ANALYTICAL_OBLIGATION_FRONTIER_of_quantitative
    (checkpoint : ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT) :
    ANALYTICAL_OBLIGATION_FRONTIER :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_positiveSpacetimeCheckpoint
    (ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT_of_quantitative checkpoint)

/-- Quantitative checkpoint directly to the final `B ↔ GR` proposition. -/
theorem NSE_GR_FINAL_B_EQUIVALENCE_of_quantitative
    (checkpoint : ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_OF_ANALYTICAL_OBLIGATION_FRONTIER
    (ANALYTICAL_OBLIGATION_FRONTIER_of_quantitative checkpoint)

end
end NSEGR.Strengthening
