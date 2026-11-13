import FourierHodgeLaws.ParameterSmoothing

/-!
Isolated proof-body endpoint: ME11
Upstream: NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterSmoothing.lean#L195
Source SHA256: 693e24c88e42270212ba4d6053b9141fcf2d1bbb983ab04bf6bfc43dbb870b0d
Original source lines: 195-228
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime
open Set Filter
open scoped BigOperators ContDiff Topology

noncomputable section

theorem _root_.GRTemp.ME11.endpoint (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f)
    {z : ℝ × Vec} (hz : 0 < z.1) :
    HasFDerivAt (inverseScalarSeries f) (inverseScalarSeriesDerivative f z) z := by
  let T : ℝ := z.1 + 1
  let s : Set (ℝ × Vec) := Ioo (0 : ℝ) T ×ˢ (univ : Set Vec)
  obtain ⟨Mt, hMtSum, _, hMt⟩ := uniform_inverseScalarCoeff_moment_bound
    (fun t => scalarTimeDerivative f t) (scalarTimeDerivative_smooth hf)
    (scalarTimeDerivative_periodic hp) T 0
  obtain ⟨Mx, hMxSum, _, hMx⟩ := uniform_inverseScalarCoeff_moment_bound f hf hp T 1
  let M : Frequency → ℝ := fun k => Mt k * ‖timeProjection‖ +
    Mx k * ‖ContinuousLinearMap.snd ℝ ℝ Vec‖
  have hMsum : Summable M :=
    (hMtSum.mul_right ‖timeProjection‖).add
      (hMxSum.mul_right ‖ContinuousLinearMap.snd ℝ ℝ Vec‖)
  have hsOpen : IsOpen s := isOpen_Ioo.prod isOpen_univ
  have hsConvex : Convex ℝ s := (convex_Ioo (0 : ℝ) T).prod convex_univ
  have hzS : z ∈ s := ⟨⟨hz, by dsimp [T]; linarith⟩, mem_univ _⟩
  have hbound (k : Frequency) (y : ℝ × Vec) (hy : y ∈ s) :
      ‖inverseScalarSeriesTermDerivative f k y‖ ≤ M k := by
    have ht : y.1 ∈ Icc (0 : ℝ) T := ⟨hy.1.1.le, hy.1.2.le⟩
    have hbt : ‖inverseScalarCoeff (scalarTimeDerivative f y.1) k‖ ≤ Mt k := by
      simpa only [pow_zero, mul_one] using hMt y.1 ht k
    have hbx : ‖inverseScalarCoeff (f y.1) k‖ *
        ‖SingularClosure.fourierPhaseCLM k‖ ≤ Mx k := by
      simpa only [pow_one] using hMx y.1 ht k
    exact (inverseScalarSeriesTermDerivative_bound f k y).trans
      (add_le_add (mul_le_mul_of_nonneg_right hbt (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hbx (norm_nonneg _)))
  have hd := hasFDerivAt_tsum_of_isPreconnected hMsum hsOpen hsConvex.isPreconnected
    (fun k y hy => inverseScalarSeriesTerm_hasFDerivAt f hf k hy.1.1)
    hbound hzS (inverseScalarSeriesTerm_summable f hf hp hz.le) hzS
  rw [tsum_inverseScalarSeriesTermDerivative f hf hp hz.le] at hd
  exact hd

end

end NSEMaxwell.HodgeProof
