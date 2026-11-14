import GRAssembly.Strengthening.Correspondence

/-! Canonical equivalence extracted from the biunique physical relation. -/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem NSE_GR_ANALYTIC_FORWARD_FAMILY_EQUIV
    (ν ρ : ℝ) (_hν : 0 < ν) (hρ : ρ ≠ 0)
    (a : Field) (ha : NSEMaxwell.Classical.Data a) :
    Nonempty (AnalyticForwardTrajectory ν a ≃ GRForwardFamily ν ρ a) :=
  ⟨analyticForwardGRFamilyEquiv ν ρ hρ a ha⟩

theorem analyticForwardGRFamilyEquiv_graph
    {ν ρ : ℝ} {a : Field} (hρ : ρ ≠ 0)
    (ha : NSEMaxwell.Classical.Data a)
    (s : AnalyticForwardTrajectory ν a)
    (γ : GRForwardFamily ν ρ a) :
    analyticForwardGRFamilyEquiv ν ρ hρ a ha s = γ ↔
      NSEGRCorresponds hρ s γ :=
  (nseGRCorresponds_iff_equiv_eq hρ ha s γ).symm

end
end NSEGR.Strengthening
