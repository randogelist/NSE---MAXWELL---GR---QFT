import FourierHodgeLaws.ParameterSmoothing

/-!
Isolated proof-body endpoint: ME10
Upstream: NSEMaxwell.HodgeProof.scalarL_trajectory_smooth
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterSmoothing.lean#L273
Source SHA256: 693e24c88e42270212ba4d6053b9141fcf2d1bbb983ab04bf6bfc43dbb870b0d
Original source lines: 273-280
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime
open Set Filter
open scoped BigOperators ContDiff Topology

noncomputable section

theorem _root_.GRTemp.ME10.endpoint {f : Pressure}
    (hf : SmoothPressure f) (hp : PeriodicPressure f) :
    SmoothPressure (fun t => scalarL (f t)) := by
  have h := Complex.reCLM.contDiff.comp_contDiffOn (inverseScalarSeries_contDiffOn f hf hp)
  apply h.congr
  intro z hz
  exact congrFun (scalarL_eq_realFourierSeries (f z.1)
    (cubeSlice_contDiff f hf hz) (hp z.1 hz)) z.2

end

end NSEMaxwell.HodgeProof
