import GRAssembly.Strengthening.TraceEndpoint
import GRAssembly.Strengthening.AnalyticPressure

/-!
The remaining source smoothing endpoint concerns only the actual velocity
of each normalized forward source. Actual NSE pressure analyticity and the
all-Sobolev source trace are derived. The root remains conditional on this
velocity endpoint and the positive-profile smooth boundary extension.
No inhabitant of either remaining analytic endpoint is asserted here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff Topology

namespace NSEGR.Strengthening
noncomputable section

def PositiveTimeVelocityAnalyticityEndpoint (ν : ℝ) (a : Field) : Prop :=
  ∀ s : NormalizedForwardTrajectory ν a,
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => s.totalVelocity z.1 z.2) positiveSpacetime

theorem NormalizedForwardTrajectory.originNormalize_totalPressure
    {ν : ℝ} {a : Field} (s : NormalizedForwardTrajectory ν a) :
    originNormalize s.totalPressure = s.totalPressure := by
  funext t x
  by_cases ht : 0 ≤ t
  · simp only [originNormalize, s.totalPressure_zero ht, sub_zero]
  · simp only [originNormalize, NormalizedForwardTrajectory.totalPressure,
      dif_neg ht, sub_zero]

theorem positiveTimeSmoothingEndpoint_of_velocity_analyticity
    {ν : ℝ} {a : Field} (hV : PositiveTimeVelocityAnalyticityEndpoint ν a) :
    PositiveTimeSmoothingEndpoint ν a := by
  intro s
  refine ⟨hV s, ?_⟩
  simpa only [s.originNormalize_totalPressure] using
    nssolution_originNormalize_positive_analytic s.solution (hV s)

theorem positiveTimeVelocityAnalyticityEndpoint_of_smoothing
    {ν : ℝ} {a : Field} (hS : PositiveTimeSmoothingEndpoint ν a) :
    PositiveTimeVelocityAnalyticityEndpoint ν a :=
  fun s => (hS s).1

theorem positiveTimeSmoothingEndpoint_iff_velocity_analyticity (ν : ℝ) (a : Field) :
    PositiveTimeSmoothingEndpoint ν a ↔ PositiveTimeVelocityAnalyticityEndpoint ν a :=
  ⟨positiveTimeVelocityAnalyticityEndpoint_of_smoothing,
    positiveTimeSmoothingEndpoint_of_velocity_analyticity⟩

def trajectoryGRFamilyEquivOfVelocityAnalyticity
    {ν : ℝ} {a : Field} (ρ : ℝ) (hρ : ρ ≠ 0)
    (hV : PositiveTimeVelocityAnalyticityEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a :=
  trajectoryGRFamilyEquiv ρ hρ
    (positiveTimeSmoothingEndpoint_of_velocity_analyticity hV)
    (smoothTrajectoryTraceEndpoint ν a) hE

theorem NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_VELOCITY_ANALYTICITY_AND_BOUNDARY
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0)
    (a : Field) (ha : NSEMaxwell.Classical.Data a)
    (hV : PositiveTimeVelocityAnalyticityEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    Nonempty (NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a) :=
  NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_SMOOTHING_AND_BOUNDARY
    ν ρ hν hρ a ha (positiveTimeSmoothingEndpoint_of_velocity_analyticity hV) hE

theorem nssolution_nonempty_gr_family_iff_of_velocity_analyticity_and_boundary
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field)
    (hV : PositiveTimeVelocityAnalyticityEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    (∃ (u : Velocity) (p : Pressure), NSEMaxwell.Classical.NSSolution ν a u p) ↔
      Nonempty (GRForwardFamily ν ρ a) :=
  nssolution_nonempty_gr_family_iff_of_analytic_endpoints ν ρ hρ a
    (positiveTimeSmoothingEndpoint_of_velocity_analyticity hV)
    (smoothTrajectoryTraceEndpoint ν a) hE

end
end NSEGR.Strengthening
