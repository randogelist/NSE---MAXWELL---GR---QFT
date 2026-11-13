import NSEMaxwellReverse
import NSEMaxwell.AnalyticReduction

/-!
# Reverse implication from the four remaining Fourier/Hodge laws

The premise is the existing concrete structure. No inhabitant is supplied.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical

/-- The exact reverse direction with the four remaining analytic fields explicit. -/
theorem maxwellB_implies_feffermanB_of_fourierHodgeLaws
    (laws : FourierHodgeLaws) (ν c : ℝ) :
    MaxwellB ν c → FeffermanB ν :=
  maxwellB_implies_feffermanB_of_periodicAnalyticLaws
    laws.toPeriodicAnalyticLaws ν c

end NSEMaxwell.Bridge
