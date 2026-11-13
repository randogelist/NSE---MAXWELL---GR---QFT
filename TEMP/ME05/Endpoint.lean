import FourierHodgeLaws.SpatialMultiplier

/-!
Isolated proof-body endpoint: ME05
Upstream: NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/SpatialMultiplier.lean#L95
Source SHA256: 9385b39dbebac0062302f458c2e4d6e0b3f072330bc81e896f2907b463de3d9f
Original source lines: 95-110
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

theorem _root_.GRTemp.ME05.endpoint (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) (j : Fin 3) :
    coordinateDerivative (vectorL F) j = vectorL (coordinateDerivative F j) := by
  have hD := NSEMaxwell.CurlCurl.coordinateDerivative_smooth hF j
  have hpD := NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic hp j
  change SingularClosure.coordinateDerivative (vectorL F) j = _
  rw [vectorL_eq_smoothFourierSynthesis F hF hp,
    SingularClosure.smoothFourierSynthesis_coordinateDerivative _
      (rapid_inverseLaplacianCoeff F hF hp) j,
    vectorL_eq_smoothFourierSynthesis (coordinateDerivative F j) hD hpD]
  congr 1
  funext k i
  unfold inverseVectorCoeff
  rw [datumFourierCoeff_coordinateDerivative F hF hp j]
  simp only [SingularClosure.spectralMultiplier]
  ring

end

end NSEMaxwell.HodgeProof
