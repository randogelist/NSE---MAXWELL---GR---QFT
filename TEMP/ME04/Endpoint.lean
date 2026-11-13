import FourierHodgeLaws.CosineMultiplier

/-!
Isolated proof-body endpoint: ME04
Upstream: NSEMaxwell.HodgeProof.vectorL_component
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/CosineMultiplier.lean#L162
Source SHA256: d12c8efdffdbf21e98aed74ed436032e314343f7aa80df61d4ad3e6ee4accc42
Original source lines: 162-170
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

theorem _root_.GRTemp.ME04.endpoint (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) (i : Fin 3) :
    (fun x => vectorL F x i) = scalarL (fun x => F x i) := by
  have hfi : ContDiff ℝ ∞ (fun x => F x i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hF
  have hpi : SpatialPeriodic (fun x => F x i) := fun x j => congrArg (fun v : Vec => v i) (hp x j)
  rw [vectorL_eq_smoothFourierSynthesis F hF hp,
    scalarL_eq_realFourierSeries (fun x => F x i) hfi hpi]
  rfl

end

end NSEMaxwell.HodgeProof
