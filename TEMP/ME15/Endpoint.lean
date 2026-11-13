import FourierHodgeLaws.ParameterIntegral

/-!
Isolated proof-body endpoint: ME15
Upstream: NSEMaxwell.HodgeProof.scalarMean_contDiffOn
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterIntegral.lean#L50
Source SHA256: e057005dbf269c7fd797241224651d9f145272f9674f50faa24e2e3dba2e7fe7
Original source lines: 50-59
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.TemporalMean
open Set MeasureTheory
open scoped ContDiff

noncomputable section

theorem _root_.GRTemp.ME15.endpoint (f : Pressure) (hf : SmoothPressure f) :
    ContDiffOn ℝ ∞ (fun t : ℝ => scalarMean (f t)) (Ici (0 : ℝ)) := by
  let u : Velocity := fun t x => f t x • unitVector 0
  have hu : SmoothVelocity u := hf.smul contDiffOn_const
  have hm := spatialMean_contDiffOn u hu
  have hc : ContDiffOn ℝ ∞ (fun t : ℝ => spatialMean (u t) 0) (Ici (0 : ℝ)) :=
    (contDiffOn_piLp 2).mp hm 0
  apply hc.congr
  intro t ht
  exact (spatialMean_scalar_embed (f t)).symm

end

end NSEMaxwell.HodgeProof
