import FourierHodgeLaws.CosineMultiplier

/-!
Isolated proof-body endpoint: ME01
Upstream: NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/CosineMultiplier.lean#L72
Source SHA256: d12c8efdffdbf21e98aed74ed436032e314343f7aa80df61d4ad3e6ee4accc42
Original source lines: 72-84
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

theorem _root_.GRTemp.ME01.endpoint (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    scalarL f = SingularClosure.realFourierSeries (inverseScalarCoeff f) := by
  funext x
  have hs := SingularClosure.scalarFourierSeries_summable
    (rapid_inverseScalarCoeff f hf hp).summable_norm x
  have hre := Complex.reCLM.map_tsum hs
  simp only [Complex.reCLM_apply] at hre
  unfold scalarL SingularClosure.realFourierSeries SingularClosure.scalarFourierSeries
  rw [hre]
  apply tsum_congr
  intro k
  exact scalar_cosine_summand f hf.continuous k x

end

end NSEMaxwell.HodgeProof
