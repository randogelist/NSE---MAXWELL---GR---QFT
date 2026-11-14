import GRAssembly.Strengthening.AnalyticBEquivalence

/-!
Single-endpoint final closure adapter.

Every relation-first and geometric theorem is upstream of this file. The only
remaining premise is `ANALYTICAL_OBLIGATION_FRONTIER`: datumwise selection of
one positive-time analytic normalized trajectory whenever the smooth normalized
source carrier is nonempty. Supplying one inhabitant closes the literal
Fefferman-B/GR-family equivalence by deterministic composition.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

/-- The sole remaining premise for the literal proposition-level root. -/
def ANALYTICAL_OBLIGATION_FRONTIER : Prop :=
  ∀ (ν : ℝ), 0 < ν → DatumwiseAnalyticSelection ν

/-- Compatibility alias for the former premise name. -/
abbrev NSE_GR_FINAL_ANALYTIC_SELECTION_CERTIFICATE : Prop :=
  ANALYTICAL_OBLIGATION_FRONTIER

/-- The final unconditional proposition to be obtained after the frontier. -/
def NSE_GR_FINAL_B_EQUIVALENCE : Prop :=
  ∀ (ν ρ : ℝ), 0 < ν → ρ ≠ 0 →
    (NSEMaxwell.Classical.FeffermanB ν ↔ GRFamilyB ν ρ)

theorem finalPositiveTimeAnalyticSelection_of_frontier
    (frontier : ANALYTICAL_OBLIGATION_FRONTIER)
    (ν : ℝ) (hν : 0 < ν) :
    PositiveTimeAnalyticSelection ν :=
  datumwiseAnalyticSelection_implies_positiveTimeAnalyticSelection
    (frontier ν hν)

theorem finalPositiveTimeAnalyticSelection_of_certificate
    (certificate : NSE_GR_FINAL_ANALYTIC_SELECTION_CERTIFICATE)
    (ν : ℝ) (hν : 0 < ν) :
    PositiveTimeAnalyticSelection ν :=
  finalPositiveTimeAnalyticSelection_of_frontier certificate ν hν

theorem ANALYTICAL_OBLIGATION_FRONTIER_of_velocityAnalyticity
    (hV : ∀ (ν : ℝ), 0 < ν →
      ∀ a : Field, NSEMaxwell.Classical.Data a →
        PositiveTimeVelocityAnalyticityEndpoint ν a) :
    ANALYTICAL_OBLIGATION_FRONTIER := by
  intro ν hν
  exact datumwiseAnalyticSelection_of_velocityAnalyticity (hV ν hν)

theorem finalCertificate_of_velocityAnalyticity
    (hV : ∀ (ν : ℝ), 0 < ν →
      ∀ a : Field, NSEMaxwell.Classical.Data a →
        PositiveTimeVelocityAnalyticityEndpoint ν a) :
    NSE_GR_FINAL_ANALYTIC_SELECTION_CERTIFICATE :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_velocityAnalyticity hV

theorem NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTICAL_OBLIGATION_FRONTIER
    (frontier : ANALYTICAL_OBLIGATION_FRONTIER)
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0) :
    NSEMaxwell.Classical.FeffermanB ν ↔ GRFamilyB ν ρ :=
  NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTIC_SELECTION ν ρ hν hρ
    (finalPositiveTimeAnalyticSelection_of_frontier frontier ν hν)

theorem NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_FINAL_CERTIFICATE
    (certificate : NSE_GR_FINAL_ANALYTIC_SELECTION_CERTIFICATE)
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0) :
    NSEMaxwell.Classical.FeffermanB ν ↔ GRFamilyB ν ρ :=
  NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTICAL_OBLIGATION_FRONTIER
    certificate ν ρ hν hρ

theorem NSE_GR_FINAL_B_EQUIVALENCE_OF_ANALYTICAL_OBLIGATION_FRONTIER
    (frontier : ANALYTICAL_OBLIGATION_FRONTIER) :
    NSE_GR_FINAL_B_EQUIVALENCE := by
  intro ν ρ hν hρ
  exact NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTICAL_OBLIGATION_FRONTIER
    frontier ν ρ hν hρ

theorem NSE_GR_FINAL_B_EQUIVALENCE_OF_CERTIFICATE
    (certificate : NSE_GR_FINAL_ANALYTIC_SELECTION_CERTIFICATE) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_OF_ANALYTICAL_OBLIGATION_FRONTIER certificate

end
end NSEGR.Strengthening
