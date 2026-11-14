import GRAssembly.Strengthening.AnalyticalFrontier.CheckpointFactorial

/-!
Checkpoint edges: pointwise analyticity gives the exact positive-spacetime
endpoint, which gives the named datumwise selection frontier.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT_of_pointwise
    (checkpoint : ANALYTICAL_POINTWISE_CHECKPOINT) :
    ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT := by
  intro ν hν a ha s z hz
  exact checkpoint ν hν a ha s z hz

theorem ANALYTICAL_OBLIGATION_FRONTIER_of_positiveSpacetimeCheckpoint
    (checkpoint : ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT) :
    ANALYTICAL_OBLIGATION_FRONTIER :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_velocityAnalyticity checkpoint

theorem ANALYTICAL_OBLIGATION_FRONTIER_of_factorialCheckpoint
    (checkpoint : ANALYTICAL_FACTORIAL_CHECKPOINT) :
    ANALYTICAL_OBLIGATION_FRONTIER :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_positiveSpacetimeCheckpoint
    (ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT_of_pointwise
      (ANALYTICAL_POINTWISE_CHECKPOINT_of_factorial checkpoint))

end
end NSEGR.Strengthening
