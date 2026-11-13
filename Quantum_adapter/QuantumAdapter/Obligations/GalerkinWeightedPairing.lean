import QuantumAdapter.Obligations.GalerkinWeightedPhase
import QuantumAdapter.Obligations.EnergyConvection

/-! Exact weighted convection pairing before applying analytic estimates. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

theorem complex_real_weight_pair (a : ℝ) (z w : ℂ) :
    (star ((a : ℂ) * z) * ((a : ℂ) * w)).re = a ^ 2 * (star z * w).re := by
  simp [Complex.star_def, Complex.mul_re, Complex.mul_im]
  ring

theorem sobolevWeighted_inner_eq_sum (s N : ℕ) (q r : Phase N) :
    inner ℝ (sobolevWeightedPhaseCLM s N q) (sobolevWeightedPhaseCLM s N r) =
      ∑ k ∈ fullModes N, torusSobolevWeight k ^ (2 * s) *
        ∑ i : Fin 3, (star (phaseCoeff q k i) * phaseCoeff r k i).re := by
  change inner ℝ (sobolevWeightedPhase s N q) (sobolevWeightedPhase s N r) = _
  rw [phase_inner_eq_sum]
  simp only [sobolevWeightedPhase_coeff, sobolevWeightedCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := complex_real_weight_pair (torusSobolevWeight k ^ s)
    (phaseCoeff q k i) (phaseCoeff r k i)
  simpa only [Complex.ofReal_pow, ← pow_mul, Nat.mul_comm] using h

theorem sobolevWeighted_inner_bilinearConvection (s N : ℕ)
    (e q r : Phase N) :
    inner ℝ (sobolevWeightedPhaseCLM s N e)
      (sobolevWeightedPhaseCLM s N (bilinearConvection N q r)) =
      -(∑ k ∈ fullModes N, torusSobolevWeight k ^ (2 * s) *
        ∑ i : Fin 3, (star (phaseCoeff e k i) *
          fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i).re) := by
  rw [sobolevWeighted_inner_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [phaseCoeff_bilinearConvection, if_pos hk, mul_neg,
    Complex.neg_re, Finset.sum_neg_distrib]
  have hp := congrArg Complex.re
    (coefficientLeray_pairing k (phaseCoeff e k)
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k)
      (phaseCoeff_solenoidal e k))
  simp only [Complex.re_sum] at hp
  rw [hp]
  ring

end
end QuantumAdapter.Obligations
