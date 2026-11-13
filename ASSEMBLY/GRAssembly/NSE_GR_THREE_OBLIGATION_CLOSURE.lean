import GRAssembly.RootClosure

/-! Exact delivery endpoint for the three-obligation composition.
The literal literature inputs remain explicit theorem premises. -/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly

theorem NSE_GR_THREE_OBLIGATION_CLOSURE
    (ν ρ t0 : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0) (input : LiteratureInputs) :
    ExactSectorEquivalence ν ρ t0 :=
  NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_LITERATURE_INPUTS ν ρ t0 hν hρ input

end NSEGR.Assembly
