import GRAssembly.Strengthening.SmoothingEndpoint
import GRAssembly.Strengthening.BoundaryEndpoint
import GRAssembly.Strengthening.BEquivalence
import GRAssembly.Strengthening.ChainFormulas
import GRAssembly.Strengthening.InitialPDE
import GRAssembly.Strengthening.ReverseChain

/-!
Conditional exact root: one named positive-time velocity analyticity endpoint.
Boundary extension, source trace, pressure analyticity, actual geometric
carrier semantics and inverse formulas are supplied by the imported chain.
The remaining endpoint has no asserted inhabitant in this module.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def derivedBoundaryGRFamilyEquiv
    {ν : ℝ} {a : Field} (ρ : ℝ) (hρ : ρ ≠ 0)
    (ha : NSEMaxwell.Classical.Data a)
    (hV : PositiveTimeVelocityAnalyticityEndpoint ν a) :
    NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a :=
  trajectoryGRFamilyEquivOfVelocityAnalyticity ρ hρ hV
    (positiveProfileBoundaryEndpoint ν a ha)

theorem NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_VELOCITY_ANALYTICITY
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0)
    (a : Field) (ha : NSEMaxwell.Classical.Data a)
    (hV : PositiveTimeVelocityAnalyticityEndpoint ν a) :
    Nonempty (NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a) :=
  NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_VELOCITY_ANALYTICITY_AND_BOUNDARY
    ν ρ hν hρ a ha hV (positiveProfileBoundaryEndpoint ν a ha)

theorem NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_VELOCITY_ANALYTICITY
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0)
    (hV : ∀ a : Field, NSEMaxwell.Classical.Data a →
      PositiveTimeVelocityAnalyticityEndpoint ν a) :
    NSEMaxwell.Classical.FeffermanB ν ↔ GRFamilyB ν ρ :=
  NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTIC_ENDPOINTS ν ρ hν hρ
    (fun a ha => positiveTimeSmoothingEndpoint_of_velocity_analyticity (hV a ha))
    (fun a ha => positiveProfileBoundaryEndpoint ν a ha)

end
end NSEGR.Strengthening
