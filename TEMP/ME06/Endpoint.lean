import FourierHodgeLaws.SpatialMultiplier

/-!
Isolated proof-body endpoint: ME06
Upstream: NSEMaxwell.HodgeProof.divergence_vectorL_commute
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/SpatialMultiplier.lean#L127
Source SHA256: 9385b39dbebac0062302f458c2e4d6e0b3f072330bc81e896f2907b463de3d9f
Original source lines: 127-141
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

theorem _root_.GRTemp.ME06.endpoint (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) :
    NSEMaxwell.Classical.divergence (vectorL F) =
      scalarL (NSEMaxwell.Classical.divergence F) := by
  have hsum := scalarL_finset_sum Finset.univ
    (fun j : Fin 3 => fun x => coordinateDerivative F j x j)
    (fun j => NSEMaxwell.CurlCurl.coordinate_component_smooth hF j j)
    (fun j => coordinate_component_periodic F hp j j)
  funext x
  change (∑ j : Fin 3, coordinateDerivative (vectorL F) j x j) = _
  rw [show NSEMaxwell.Classical.divergence F =
    (fun y => ∑ j : Fin 3, coordinateDerivative F j y j) from rfl, hsum]
  apply Finset.sum_congr rfl
  intro j _
  exact (scalarL_coordinateComponent F hF hp j j x).symm

end

end NSEMaxwell.HodgeProof
