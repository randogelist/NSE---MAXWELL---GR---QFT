import FourierHodgeLaws.ParameterCoefficients

/-!
Isolated proof-body endpoint: ME13
Upstream: NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterCoefficients.lean#L206
Source SHA256: 016d9cf0c1deda75770d39f66c2e5c684435448bc7c9785cbc5d28612db54eee
Original source lines: 206-210
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

theorem _root_.GRTemp.ME13.endpoint (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => scalarCoeff (f s) k)
      (scalarCoeff (scalarTimeDerivative f t) k) t :=
  (scalarCoeff_hasDerivWithinAt f hf k ht.le).hasDerivAt (Ici_mem_nhds ht)

end

end NSEMaxwell.HodgeProof
