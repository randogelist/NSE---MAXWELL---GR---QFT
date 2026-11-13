import FourierHodgeLaws.SpatialInhabitant

/-!
Isolated proof-body endpoint: ME08
Upstream: NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/SpatialInhabitant.lean#L15
Source SHA256: 4a414a1125fffa62e0e4f760186fc1597cb116052c138ec3a486a0cb7c6b693f
Original source lines: 15-19
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge

noncomputable section

theorem _root_.GRTemp.ME08.endpoint : SpatialInverseLaplacianLaws where
  vector_smooth := vectorL_smooth
  curl_commute := curl_vectorL_commute
  divergence_commute := divergence_vectorL_commute
  poisson := neg_laplacian_vectorL

end

end NSEMaxwell.HodgeProof
