import GRAssembly.Strengthening.AnalyticalFrontier.CheckpointSelection

/-!
Final checkpoint composition.

No analytic proof is hidden here. The only unresolved input is the explicit
`ANALYTICAL_FACTORIAL_CHECKPOINT`; all later arrows are deterministic.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem NSE_GR_FINAL_B_EQUIVALENCE_of_positiveSpacetimeCheckpoint
    (checkpoint : ANALYTICAL_POSITIVE_SPACETIME_CHECKPOINT) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_OF_ANALYTICAL_OBLIGATION_FRONTIER
    (ANALYTICAL_OBLIGATION_FRONTIER_of_positiveSpacetimeCheckpoint checkpoint)

theorem NSE_GR_FINAL_B_EQUIVALENCE_of_factorialCheckpoint
    (checkpoint : ANALYTICAL_FACTORIAL_CHECKPOINT) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_OF_ANALYTICAL_OBLIGATION_FRONTIER
    (ANALYTICAL_OBLIGATION_FRONTIER_of_factorialCheckpoint checkpoint)

end
end NSEGR.Strengthening
