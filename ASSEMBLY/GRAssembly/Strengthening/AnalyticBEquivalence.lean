import GRAssembly.Strengthening.RelationEquiv
import GRAssembly.Strengthening.BEquivalence
import GRAssembly.Strengthening.SmoothingEndpoint

/-!
Existence-level factorization.

The analytic-source/GR-family equivalence is unconditional. The literal
Fefferman-B equivalence has one named remaining endpoint:
`PositiveTimeAnalyticSelection`.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def AnalyticFeffermanB (ν : ℝ) : Prop :=
  ∀ a : Field, NSEMaxwell.Classical.Data a →
    Nonempty (AnalyticForwardTrajectory ν a)

theorem ANALYTIC_NSE_B_IFF_GR_BOUNDARY_FAMILY
    (ν ρ : ℝ) (_hν : 0 < ν) (hρ : ρ ≠ 0) :
    AnalyticFeffermanB ν ↔ GRFamilyB ν ρ := by
  constructor
  · intro hA a ha
    obtain ⟨s⟩ := hA a ha
    exact ⟨analyticForwardGRFamilyEquiv ν ρ hρ a ha s⟩
  · intro hG a ha
    obtain ⟨γ⟩ := hG a ha
    exact ⟨(analyticForwardGRFamilyEquiv ν ρ hρ a ha).symm γ⟩

theorem analyticFeffermanB_implies_feffermanB
    {ν : ℝ} (hA : AnalyticFeffermanB ν) :
    NSEMaxwell.Classical.FeffermanB ν := by
  intro a ha
  obtain ⟨s⟩ := hA a ha
  exact (literal_nssolution_nonempty_normalized_source ν a).mpr
    ⟨s.trajectory⟩

def DatumwiseAnalyticSelection (ν : ℝ) : Prop :=
  ∀ a : Field, NSEMaxwell.Classical.Data a →
    Nonempty (NormalizedForwardTrajectory ν a) →
    Nonempty (AnalyticForwardTrajectory ν a)

def PositiveTimeAnalyticSelection (ν : ℝ) : Prop :=
  NSEMaxwell.Classical.FeffermanB ν → AnalyticFeffermanB ν

theorem datumwiseAnalyticSelection_implies_positiveTimeAnalyticSelection
    {ν : ℝ} (hS : DatumwiseAnalyticSelection ν) :
    PositiveTimeAnalyticSelection ν := by
  intro hB a ha
  apply hS a ha
  exact (feffermanB_iff_normalized_source_nonempty ν).mp hB a ha

theorem datumwiseAnalyticSelection_of_velocityAnalyticity
    {ν : ℝ}
    (hV : ∀ a : Field, NSEMaxwell.Classical.Data a →
      PositiveTimeVelocityAnalyticityEndpoint ν a) :
    DatumwiseAnalyticSelection ν := by
  intro a ha h
  obtain ⟨s⟩ := h
  exact ⟨⟨s, hV a ha s⟩⟩

theorem positiveTimeAnalyticSelection_of_velocityAnalyticity
    {ν : ℝ}
    (hV : ∀ a : Field, NSEMaxwell.Classical.Data a →
      PositiveTimeVelocityAnalyticityEndpoint ν a) :
    PositiveTimeAnalyticSelection ν :=
  datumwiseAnalyticSelection_implies_positiveTimeAnalyticSelection
    (datumwiseAnalyticSelection_of_velocityAnalyticity hV)

theorem NSE_B_IFF_GR_BOUNDARY_FAMILY_OF_ANALYTIC_SELECTION
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0)
    (hS : PositiveTimeAnalyticSelection ν) :
    NSEMaxwell.Classical.FeffermanB ν ↔ GRFamilyB ν ρ := by
  constructor
  · intro hB
    exact (ANALYTIC_NSE_B_IFF_GR_BOUNDARY_FAMILY ν ρ hν hρ).mp
      (hS hB)
  · intro hG
    exact analyticFeffermanB_implies_feffermanB
      ((ANALYTIC_NSE_B_IFF_GR_BOUNDARY_FAMILY ν ρ hν hρ).mpr hG)

theorem GR_BOUNDARY_FAMILY_IMPLIES_NSE_B_RELATION_FIRST
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0) :
    GRFamilyB ν ρ → NSEMaxwell.Classical.FeffermanB ν := by
  intro hG
  exact analyticFeffermanB_implies_feffermanB
    ((ANALYTIC_NSE_B_IFF_GR_BOUNDARY_FAMILY ν ρ hν hρ).mpr hG)

end
end NSEGR.Strengthening
