import QuantumAdapter.Obligations.GalerkinEnergyEstimates

/-! Actual nonlinear Sobolev norm bounds for the time-jet construction. -/
set_option autoImplicit false
set_option Elab.async true
open scoped BigOperators
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

theorem coefficientLeray_norm_square_sum_le (k : Frequency) (v : Fin 3 → ℂ) :
    (∑ i : Fin 3, ‖coefficientLeray k v i‖^2) ≤ ∑ i : Fin 3, ‖v i‖^2 := by
  let w := coefficientLeray k v
  have hp := congrArg Complex.re
    (coefficientLeray_pairing k w v (coefficientLeray_solenoidal k v))
  have hz (z : ℂ) : (star z*z).re=‖z‖^2 := by
    simpa using complex_real_weight_inner 1 z
  change (∑ i : Fin 3, star (w i)*w i).re = (∑ i : Fin 3, star (w i)*v i).re at hp
  simp only [Complex.re_sum, hz] at hp
  have h : (∑ i : Fin 3, ‖w i‖^2) ≤ ∑ i : Fin 3, ‖w i‖*‖v i‖ := by
    rw [hp]
    apply Finset.sum_le_sum
    intro i hi
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq
      (by rw [norm_mul, norm_star]))
  have hn : 0 ≤ ∑ i : Fin 3, ‖w i‖^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hv : 0 ≤ ∑ i : Fin 3, ‖v i‖^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hs := (pow_le_pow_left₀ hn h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖w i‖) (fun i => ‖v i‖))
  change (∑ i : Fin 3, ‖w i‖^2) ≤ ∑ i : Fin 3, ‖v i‖^2
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  nlinarith

theorem finite_three_complex_sum_square_le (v : Fin 3 → ℂ) :
    ‖∑ j : Fin 3, v j‖^2 ≤ 3*∑ j : Fin 3, ‖v j‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun _ => (1:ℝ)) (fun j => ‖v j‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans h

theorem weighted_bilinear_coefficient_square_le (m N : ℕ) (q r : Phase N)
    (k : Frequency) (hk : k ∈ fullModes N) :
    sobolevEnergyDensity m (phaseCoeff (bilinearConvection N q r)) k ≤
      3 * ∑ i : Fin 3, ∑ j : Fin 3,
        (torusSobolevWeight k^(m+1)*‖fullTensorProduct N q r k i j‖)^2 := by
  have hp := coefficientLeray_norm_square_sum_le k
    (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k)
  have htransport (i : Fin 3) :
      ‖fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i‖^2 ≤
        3*∑ j : Fin 3, (torusSobolevWeight k*‖fullTensorProduct N q r k i j‖)^2 := by
    rw [fullBilinearTransport_eq_tensor_divergence]
    apply (finite_three_complex_sum_square_le _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le_torusSobolevWeight j k)
        (norm_nonneg _)) 2
  have hweight : 0 ≤ (torusSobolevWeight k^m)^2 := sq_nonneg _
  calc
    _ = (torusSobolevWeight k^m)^2 * ∑ i : Fin 3,
        ‖coefficientLeray k (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k) i‖^2 := by
      simp only [sobolevEnergyDensity, sobolevWeightedCoeff_norm_eq,
        phaseCoeff_bilinearConvection, if_pos hk, norm_neg, mul_pow, Finset.mul_sum]
    _ ≤ (torusSobolevWeight k^m)^2 * ∑ i : Fin 3,
        ‖fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i‖^2 :=
      mul_le_mul_of_nonneg_left hp hweight
    _ ≤ (torusSobolevWeight k^m)^2 * ∑ i : Fin 3,
        3*∑ j : Fin 3, (torusSobolevWeight k*‖fullTensorProduct N q r k i j‖)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi => htransport i)) hweight
    _ = _ := by
      simp only [Finset.mul_sum, pow_succ]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- This loss of one derivative suffices to bound every finite differential expression. -/
theorem bilinearConvection_sobolevEnergy_le (m N : ℕ) (q r : Phase N) :
    sobolevEnergy m N (bilinearConvection N q r) ≤
      54*((2:ℝ)^(m+1))^2*latticeSobolevConstant *
        (sobolevEnergy 2 N r*sobolevEnergy (m+1) N q +
         sobolevEnergy 2 N q*sobolevEnergy (m+1) N r) := by
  calc
    _ ≤ ∑ k ∈ fullModes N, 3*∑ i : Fin 3, ∑ j : Fin 3,
        (torusSobolevWeight k^(m+1)*‖fullTensorProduct N q r k i j‖)^2 :=
      Finset.sum_le_sum (fun k hk => weighted_bilinear_coefficient_square_le m N q r k hk)
    _ = 3*∑ i : Fin 3, ∑ j : Fin 3, ∑ k ∈ fullModes N,
        (torusSobolevWeight k^(m+1)*‖fullTensorProduct N q r k i j‖)^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := fullModes N) (t := Finset.univ)]
    _ ≤ 3*∑ i : Fin 3, ∑ j : Fin 3,
        2*((2:ℝ)^(m+1))^2*latticeSobolevConstant *
          (sobolevEnergy 2 N r*sobolevEnergy (m+1) N q +
           sobolevEnergy 2 N q*sobolevEnergy (m+1) N r) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (fun j hj => fullTensorProduct_energy_bound (m+1) N q r i j)
    _ = _ := by simp; ring

end
end QuantumAdapter.Obligations
