import GRAssembly.Strengthening.BoundaryEndpoint
import GRAssembly.Strengthening.BEquivalence

/-!
The exact geometric-to-NSE existence direction has no velocity-smoothing
premise. Actual decoded geometric germs give a positive analytic NSE profile;
its velocity-only spatial trace yields the already derived smooth boundary
extension and the literal forward NSSolution.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem gr_family_implies_nssolution
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field)
    (ha : NSEMaxwell.Classical.Data a) (g : GRForwardFamily ν ρ a) :
    ∃ (u : Velocity) (p : Pressure), NSEMaxwell.Classical.NSSolution ν a u p := by
  let profile : PositiveTimeProfile ν a := (positiveProfileGRFamilyEquiv ν ρ hρ a).symm g
  obtain ⟨r, _hr⟩ := Quotient.exists_rep profile
  obtain ⟨u, p, hu, hp, hi, he⟩ := positiveProfileBoundaryEndpoint ν a ha r
  exact ⟨u, p, smoothProfileExtension_is_nssolution r u p hu hp hi he⟩

theorem GR_BOUNDARY_FAMILY_IMPLIES_NSE_B
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (hGR : GRFamilyB ν ρ) :
    NSEMaxwell.Classical.FeffermanB ν := by
  intro a ha
  obtain ⟨g⟩ := hGR a ha
  exact gr_family_implies_nssolution ν ρ hρ a ha g

theorem not_gr_family_of_no_nssolution
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field)
    (ha : NSEMaxwell.Classical.Data a)
    (hNo : ¬ ∃ (u : Velocity) (p : Pressure), NSEMaxwell.Classical.NSSolution ν a u p) :
    ¬ Nonempty (GRForwardFamily ν ρ a) := by
  rintro ⟨g⟩
  exact hNo (gr_family_implies_nssolution ν ρ hρ a ha g)

theorem not_GRFamilyB_of_not_FeffermanB
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (hNotB : ¬ NSEMaxwell.Classical.FeffermanB ν) :
    ¬ GRFamilyB ν ρ := by
  intro hGR
  exact hNotB (GR_BOUNDARY_FAMILY_IMPLIES_NSE_B ν ρ hρ hGR)

end
end NSEGR.Strengthening
