import GRAssembly.Strengthening.ExactChain
import GRAssembly.Strengthening.PhysicalFourier

/-! The exact all-Sobolev source trace is derived from physical smoothness. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Strengthening
noncomputable section

theorem smoothTrajectoryTraceEndpoint (ν : ℝ) (a : Field) :
    SmoothTrajectoryTraceEndpoint ν a := by
  intro s m
  refine ⟨physicalFourierCurve m s.totalVelocity, ?_, ?_, ?_⟩
  · intro t
    exact physicalFourierValue_coeff m (s.totalVelocity t.val)
      (NSEMaxwell.Classical.velocity_slice_smooth s.solution.velocity_smooth t.property.le)
      (s.solution.velocity_periodic t.val t.property.le)
  · have h := physicalFourierValue_coeff m (s.totalVelocity 0)
      (NSEMaxwell.Classical.velocity_slice_smooth s.solution.velocity_smooth le_rfl)
      (s.solution.velocity_periodic 0 le_rfl)
    simpa only [physicalFourierCurve, s.solution.initial] using h
  · exact physicalFourierCurve_initial_trace s.totalVelocity s.solution.velocity_smooth
      s.solution.velocity_periodic m

theorem NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_SMOOTHING_AND_BOUNDARY
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0)
    (a : Field) (ha : NSEMaxwell.Classical.Data a)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    Nonempty (NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a) :=
  NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_ANALYTIC_ENDPOINTS
    ν ρ hν hρ a ha hS (smoothTrajectoryTraceEndpoint ν a) hE

end
end NSEGR.Strengthening
