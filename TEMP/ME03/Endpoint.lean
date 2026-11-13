import FourierHodgeLaws.CosineMultiplier

/-!
Isolated proof-body endpoint: ME03
Upstream: NSEMaxwell.HodgeProof.vectorL_smooth
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/CosineMultiplier.lean#L144
Source SHA256: d12c8efdffdbf21e98aed74ed436032e314343f7aa80df61d4ad3e6ee4accc42
Original source lines: 144-148
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

theorem _root_.GRTemp.ME03.endpoint (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) : ContDiff ℝ ∞ (vectorL F) := by
  rw [vectorL_eq_smoothFourierSynthesis F hF hp]
  exact SingularClosure.smoothFourierSynthesis_contDiff _
    (rapid_inverseLaplacianCoeff F hF hp)

end

end NSEMaxwell.HodgeProof
