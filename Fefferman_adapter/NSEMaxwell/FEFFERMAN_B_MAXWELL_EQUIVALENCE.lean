import NSEMaxwell.AnalyticBridge
import NSEMaxwell.AnalyticReduction
import FourierHodgeLaws.Inhabitant

/-!
The original conditional entry points retain their exact types.
The unconditional entry point supplies the concrete Fourier/Hodge inhabitant
to the frozen equivalence theorem.
-/

namespace NSEMaxwell

theorem FEFFERMAN_B_MAXWELL_EQUIVALENCE
    (analyticLaws : Bridge.PeriodicAnalyticLaws) :
    Classical.ExactEquivalence :=
  Bridge.exact_equivalence_of_periodicAnalyticLaws analyticLaws

/-- Stronger entry point: five local analytic endpoints are now derived.
The four Fourier/Hodge endpoints remain explicit parameters of this API. -/
theorem FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED
    (fourierHodgeLaws : Bridge.FourierHodgeLaws) :
    Classical.ExactEquivalence :=
  Bridge.exact_equivalence_of_fourierHodgeLaws fourierHodgeLaws

/-- The frozen equivalence with all four Fourier/Hodge obligations discharged. -/
theorem FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL :
    Classical.ExactEquivalence :=
  HodgeProof.exact_equivalence_native

end NSEMaxwell
