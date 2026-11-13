import FourierHodgeLaws.PoissonFromCoefficients

/-!
Isolated proof-body endpoint: ME07
Upstream: NSEMaxwell.HodgeProof.neg_laplacian_vectorL
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/PoissonFromCoefficients.lean#L106
Source SHA256: 23cf86397aa7029712671127bbdf7fc28abcd0eafb182d7c4ca48e7afb44fd06
Original source lines: 106-149
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

theorem _root_.GRTemp.ME07.endpoint (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    -NSEMaxwell.Classical.laplacian (vectorL a) = a - (fun _ => spatialMean a) := by
  have hL := vectorL_smooth a ha hp
  have hpL := NSEMaxwell.FourierPeriodic.vectorL_periodic a
  have hleft : Continuous (-NSEMaxwell.Classical.laplacian (vectorL a)) :=
    (NSEMaxwell.PeriodicIntegration.laplacian_smooth hL).neg.continuous
  have hright : Continuous (a - (fun _ => spatialMean a)) :=
    ha.continuous.sub continuous_const
  have hpleft : SpatialPeriodic (-NSEMaxwell.Classical.laplacian (vectorL a)) := by
    intro x j
    change -NSEMaxwell.Classical.laplacian (vectorL a) (x + unitVector j) =
      -NSEMaxwell.Classical.laplacian (vectorL a) x
    rw [NSEMaxwell.PeriodicIntegration.laplacian_periodic hpL x j]
  have hpright : SpatialPeriodic (a - (fun _ => spatialMean a)) := by
    intro x j
    change a (x + unitVector j) - spatialMean a = a x - spatialMean a
    rw [hp x j]
  apply SingularClosure.datumFourierCoeff_injective_continuous_periodic _ _
    hleft hright hpleft hpright
  rw [datumFourierCoeff_neg, datumFourierCoeff_laplacian (vectorL a) hL hpL,
    datumFourierCoeff_vectorL a ha hp,
    datumFourierCoeff_sub a (fun _ => spatialMean a) ha.continuous continuous_const,
    datumFourierCoeff_const]
  funext k i
  change -(-(SingularClosure.laplacianFrequency k : ℂ) * inverseVectorCoeff a k i) =
    SingularClosure.datumFourierCoeff a k i -
      (if k = 0 then (spatialMean a i : ℂ) else 0)
  by_cases hk : k = 0
  · subst k
    rw [inverseVectorCoeff_zero]
    simp only [mul_zero, neg_zero, if_pos rfl]
    rw [SingularClosure.datumFourierCoeff_zero
      (NSEMaxwell.PeriodicIntegration.integrableOn_unitCube_of_continuous ha.continuous) i]
    exact (sub_self _).symm
  · rw [if_neg hk, sub_zero]
    have hmul : (SingularClosure.laplacianFrequency k : ℂ) *
        (inverseLaplacianSymbol k : ℂ) = 1 := by
      exact_mod_cast laplacianFrequency_mul_inverseLaplacianSymbol k hk
    unfold inverseVectorCoeff
    calc
      _ = ((SingularClosure.laplacianFrequency k : ℂ) *
          (inverseLaplacianSymbol k : ℂ)) * SingularClosure.datumFourierCoeff a k i := by ring
      _ = _ := by rw [hmul, one_mul]

end

end NSEMaxwell.HodgeProof
