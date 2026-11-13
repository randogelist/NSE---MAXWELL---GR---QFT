import FourierHodgeLaws.ParameterCoefficients

/-!
Isolated proof-body endpoint: ME17.E02
Upstream: NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterCoefficients.lean#L142
Source SHA256: 016d9cf0c1deda75770d39f66c2e5c684435448bc7c9785cbc5d28612db54eee
Original source lines: 142-148
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

theorem _root_.GRTemp.ME17.E02.endpoint {f : Pressure} (hp : PeriodicPressure f) :
    PeriodicPressure (fun t => scalarTimeDerivative f t) := by
  intro t ht x i
  apply derivWithin_congr
  · intro s hs
    exact hp s hs x i
  · exact hp t ht x i

end

end NSEMaxwell.HodgeProof
