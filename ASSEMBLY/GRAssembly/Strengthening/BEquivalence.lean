import GRAssembly.Strengthening.TraceEndpoint

/-! Exact B-predicate assembly. The analytic endpoint premises remain explicit. -/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def GRFamilyB (ν ρ : ℝ) : Prop :=
  ∀ a : Field, NSEMaxwell.Classical.Data a → Nonempty (GRForwardFamily ν ρ a)

theorem NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTIC_ENDPOINTS
    (ν ρ : ℝ) (_hν : 0 < ν) (hρ : ρ ≠ 0)
    (hS : ∀ a : Field, NSEMaxwell.Classical.Data a → PositiveTimeSmoothingEndpoint ν a)
    (hE : ∀ a : Field, NSEMaxwell.Classical.Data a → PositiveProfileBoundaryEndpoint ν a) :
    NSEMaxwell.Classical.FeffermanB ν ↔ GRFamilyB ν ρ := by
  constructor
  · intro hB a ha
    exact (nssolution_nonempty_gr_family_iff_of_analytic_endpoints ν ρ hρ a
      (hS a ha) (smoothTrajectoryTraceEndpoint ν a) (hE a ha)).mp (hB a ha)
  · intro hG a ha
    exact (nssolution_nonempty_gr_family_iff_of_analytic_endpoints ν ρ hρ a
      (hS a ha) (smoothTrajectoryTraceEndpoint ν a) (hE a ha)).mpr (hG a ha)

end
end NSEGR.Strengthening
