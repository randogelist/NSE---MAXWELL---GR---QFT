import GRAssembly.Strengthening.FinalSelectionClosure

/-!
Named checkpoints for the final positive-time analyticity frontier.

The first checkpoint records exactly the local factorial estimate consumed by
the already certified real-analytic closure theorem. Later checkpoints contain
no hidden analytic input: they only repackage pointwise analyticity,
`AnalyticOnNhd`, datumwise selection, and the final `B ↔ GR` root.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped Topology ContDiff

namespace NSEGR.Strengthening
noncomputable section

/--
At every positive spacetime point of every supplied normalized forward
trajectory, one has a smooth ball and a uniform factorial Fréchet-derivative
bound on that ball.
-/
def ANALYTICAL_FACTORIAL_CHECKPOINT : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : Field), NSEMaxwell.Classical.Data a →
      ∀ (s : NormalizedForwardTrajectory ν a) (z : ℝ × Vec),
        z ∈ positiveSpacetime →
          ∃ r M A : ℝ,
            0 < r ∧
            0 ≤ M ∧
            0 ≤ A ∧
            ContDiffOn ℝ ∞
              (fun w : ℝ × Vec => s.totalVelocity w.1 w.2)
              (Metric.ball z r) ∧
            ∀ n w, w ∈ Metric.ball z r →
              ‖iteratedFDeriv ℝ n
                  (fun q : ℝ × Vec => s.totalVelocity q.1 q.2) w‖ ≤
                M * A ^ n * (n.factorial : ℝ)

/-- Pointwise joint real analyticity at every positive spacetime point. -/
def ANALYTICAL_POINTWISE_CHECKPOINT : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : Field), NSEMaxwell.Classical.Data a →
      ∀ (s : NormalizedForwardTrajectory ν a) (z : ℝ × Vec),
        z ∈ positiveSpacetime →
          AnalyticAt ℝ
            (fun w : ℝ × Vec => s.totalVelocity w.1 w.2) z

/-- The exact universal positive-spacetime endpoint used by selection. -/
def ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : Field), NSEMaxwell.Classical.Data a →
      PositiveTimeVelocityAnalyticityEndpoint ν a

end
end NSEGR.Strengthening
