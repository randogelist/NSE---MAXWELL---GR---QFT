import FourierHodgeLaws.CosineMultiplier

/-!
Isolated proof-body endpoint: ME02
Upstream: NSEMaxwell.HodgeProof.scalarL_smooth
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/CosineMultiplier.lean#L157
Source SHA256: d12c8efdffdbf21e98aed74ed436032e314343f7aa80df61d4ad3e6ee4accc42
Original source lines: 157-160
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical

noncomputable section

theorem _root_.GRTemp.ME02.endpoint (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) : ContDiff ℝ ∞ (scalarL f) := by
  rw [scalarL_eq_realFourierSeries f hf hp]
  exact SingularClosure.realFourierSeries_contDiff (rapid_inverseScalarCoeff f hf hp)

end

end NSEMaxwell.HodgeProof
