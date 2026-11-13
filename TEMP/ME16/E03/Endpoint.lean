import FourierHodgeLaws.TargetPrimitives

/-!
Isolated proof-body endpoint: ME16.E03
Upstream: NSEMaxwell.HodgeProof.scalarLift_periodic
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/TargetPrimitives.lean#L63
Source SHA256: 4fffe11365b4b539a063320719565a4e220983ed9113229c9613e87c58f02158
Original source lines: 63-67
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

theorem _root_.GRTemp.ME16.E03.endpoint (f : ScalarField) (hf : SpatialPeriodic f) :
    SpatialPeriodic (scalarLift f) := by
  intro x j
  ext i
  exact hf x j

end

end NSEMaxwell.HodgeProof
