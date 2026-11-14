import GRAssembly.Strengthening.AnalyticalFrontier.CheckpointDefinitions
import GRAssembly.AnalyticHodgeTaylor

/-!
Checkpoint edge: local factorial bounds imply pointwise real analyticity.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem ANALYTICAL_POINTWISE_CHECKPOINT_of_factorial
    (checkpoint : ANALYTICAL_FACTORIAL_CHECKPOINT) :
    ANALYTICAL_POINTWISE_CHECKPOINT := by
  intro ν hν a ha s z hz
  obtain ⟨r, M, A, hr, hM, hA, hsmooth, hbound⟩ :=
    checkpoint ν hν a ha s z hz
  exact NSEGR.Assembly.analyticAt_of_iteratedFDeriv_bound
    (fun w : ℝ × Vec => s.totalVelocity w.1 w.2) z
    hr hM hA hsmooth hbound

end
end NSEGR.Strengthening
