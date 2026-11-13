import NSEMaxwellForward
import NSEMaxwell.AnalyticReduction

/-!
# Forward implication from the four remaining Fourier/Hodge laws

The premise is the existing concrete structure. No inhabitant is supplied.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical

/-- The exact forward direction with the four remaining analytic fields explicit. -/
theorem feffermanB_implies_maxwellB_of_fourierHodgeLaws
    (laws : FourierHodgeLaws) (ν c : ℝ) :
    FeffermanB ν → MaxwellB ν c :=
  feffermanB_implies_maxwellB_of_periodicAnalyticLaws
    laws.toPeriodicAnalyticLaws ν c

end NSEMaxwell.Bridge
