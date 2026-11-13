import FourierHodgeLaws.ParameterCoefficients

/-!
Isolated proof-body endpoint: ME17.E01
Upstream: NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterCoefficients.lean#L138
Source SHA256: 016d9cf0c1deda75770d39f66c2e5c684435448bc7c9785cbc5d28612db54eee
Original source lines: 138-140
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

theorem _root_.GRTemp.ME17.E01.endpoint {f : Pressure} (hf : SmoothPressure f) :
    SmoothPressure (fun t => scalarTimeDerivative f t) :=
  cubeTimeDerivative_smooth f hf

end

end NSEMaxwell.HodgeProof
