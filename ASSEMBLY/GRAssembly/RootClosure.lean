import GRAssembly.NativeInverseCanonical
import GRAssembly.NativeCompletion
import GRAssembly.NativeGluing

/-!
Deterministic composition of the actual scalar, Gaussian, reconstruction and
inverse-law constructions. The only non-foundational assumptions of the root
are the three literal literature propositions and the displayed parameters.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
noncomputable section

/-- Every native adapter record is constructed from the literal literature input. -/
theorem nativeLawPackages_of_literatureInputs
    (input : LiteratureInputs) (ν ρ t0 : ℝ) (hρ : ρ ≠ 0) :
    ∃ c : ScalarBoundaryCompletionLaws ν ρ t0,
      ∃ r : AnalyticRadialExtensionLaws ρ t0,
        ∃ h : GeometricReconstructionLaws ν ρ t0, GermInverseLaws c r h := by
  let c := scalarBoundaryCompletionLaws_of_literatureCK input.ck ν ρ t0 hρ
  let r := analyticRadialExtensionLaws_of_literatureGaussian input.gaussianJet ρ t0
  let h := geometricReconstructionLaws_native ν ρ t0
  exact ⟨c, r, h, germInverseLaws_of_literature input.ck input.gaussianJet hρ c r h⟩

/-- Exact local marked-sector root; no native law record remains an extra premise. -/
theorem NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_LITERATURE_INPUTS
    (ν ρ t0 : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0) (input : LiteratureInputs) :
    ExactSectorEquivalence ν ρ t0 := by
  obtain ⟨c, r, h, q⟩ := nativeLawPackages_of_literatureInputs input ν ρ t0 hρ
  exact NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_NAMED_CONTRACTS ν ρ t0 hν hρ c r h q

end
end NSEGR.Assembly
