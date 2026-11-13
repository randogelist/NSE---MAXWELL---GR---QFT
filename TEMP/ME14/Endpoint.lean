import FourierHodgeLaws.UniformCoefficientBounds

/-!
Isolated proof-body endpoint: ME14
Upstream: NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/UniformCoefficientBounds.lean#L155
Source SHA256: ee3d428ae138b05907a15bd3cc68d0a9afcd041b5ea400888bfaa75e1fb1402e
Original source lines: 155-168
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration

noncomputable section

theorem _root_.GRTemp.ME14.endpoint (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) (T : ℝ) (m : ℕ) :
    ∃ M : Frequency → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency,
        ‖inverseScalarCoeff (f t) k‖ * ‖SingularClosure.fourierPhaseCLM k‖ ^ m ≤ M k := by
  obtain ⟨M, hsum, hnon, hM⟩ := uniform_scalarCoeff_moment_bound f hf hp T m
  refine ⟨M, hsum, hnon, ?_⟩
  intro t ht k
  have hcoeff : ‖inverseScalarCoeff (f t) k‖ ≤ ‖scalarCoeff (f t) k‖ := by
    rw [inverseScalarCoeff, norm_mul]
    exact (mul_le_mul_of_nonneg_right (inverseLaplacianSymbol_complex_norm_le_one k)
      (norm_nonneg _)).trans_eq (one_mul _)
  exact (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (norm_nonneg _) _)).trans
    (hM t ht k)

end

end NSEMaxwell.HodgeProof
