import FourierHodgeLaws.SpatialHodge

/-!
Isolated proof-body endpoint: ME09
Upstream: NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/SpatialHodge.lean#L79
Source SHA256: 96492e65f07cc825eb9e5ae2f43de61ee3b6f4ba2c96ac85dbf44290be228df4
Original source lines: 79-88
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.FourierPeriodic
open scoped ContDiff

noncomputable section

theorem _root_.GRTemp.ME09.endpoint
    (laws : SpatialInverseLaplacianLaws) (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) :
    K (spatialCurl F) = F - (fun _ => spatialMean F) +
      NSEMaxwell.Classical.gradient (scalarL (NSEMaxwell.Classical.divergence F)) := by
  have hcomm : K (spatialCurl F) = spatialCurl (K F) := by
    unfold K
    rw [← laws.curl_commute F hF hp]
  rw [hcomm]
  exact laws.curl_K F hF hp

end

end NSEMaxwell.HodgeProof
