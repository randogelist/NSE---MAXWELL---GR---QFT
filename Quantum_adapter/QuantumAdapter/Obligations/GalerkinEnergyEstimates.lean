import SingularClosure.FourierTransport
import QuantumAdapter.Obligations.GalerkinProducts
import QuantumAdapter.Obligations.EnergyConvection
import QuantumAdapter.Obligations.GalerkinWeightedPhase
import QuantumAdapter.Obligations.ScalarGrowth

/-! Native viscous tame estimates, with no derivative loss in the energy inequality. -/
set_option autoImplicit false
set_option Elab.async true
open scoped BigOperators
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

theorem scalar_young_div (δ a b : ℝ) (hδ : 0 < δ) :
    2*a*b ≤ δ*a^2+b^2/δ := by
  calc
    _ = (2*δ*a*b)/δ := by field_simp <;> ring
    _ ≤ (δ^2*a^2+b^2)/δ :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (δ*a-b)]) hδ.le
    _ = _ := by field_simp <;> ring

theorem fullBilinearTransport_eq_tensor_divergence (N : ℕ) (q r : Phase N)
    (k : Frequency) (i : Fin 3) :
    fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i =
      ∑ j : Fin 3, derivativeSymbol j k * fullTensorProduct N q r k i j := by
  have hterm (p : Frequency) :
      (∑ j : Fin 3, phaseCoeff q p j * derivativeSymbol j (k-p)) =
        ∑ j : Fin 3, derivativeSymbol j k * phaseCoeff q p j := by
    simp_rw [derivativeSymbol_sub]
    calc
      _ = (∑ j : Fin 3, derivativeSymbol j k * phaseCoeff q p j) -
          (∑ j : Fin 3, derivativeSymbol j p * phaseCoeff q p j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [solenoidal_derivativeSymbol_sum _ (phaseCoeff_solenoidal q) p,
        sub_zero]
  unfold fullBilinearTransport
  simp_rw [hterm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold fullTensorProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

def weightedTransportPairing (m N : ℕ) (e q r : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, torusSobolevWeight k^(2*m) *
    ∑ i : Fin 3, (star (phaseCoeff e k i) *
      fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i).re

theorem weighted_triad_young (m : ℕ) (k : Frequency) (j : Fin 3)
    (z v : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    2*(torusSobolevWeight k^(2*m) *
      |(star z * (derivativeSymbol j k * v)).re|) ≤
      δ*(torusSobolevWeight k^(m+1)*‖z‖)^2 +
        (torusSobolevWeight k^m*‖v‖)^2/δ := by
  have ha : |(star z * (derivativeSymbol j k * v)).re| ≤
      ‖z‖ * (torusSobolevWeight k * ‖v‖) := by
    calc
      _ ≤ ‖star z * (derivativeSymbol j k * v)‖ := Complex.abs_re_le_norm _
      _ = ‖z‖*(‖derivativeSymbol j k‖*‖v‖) := by rw [norm_mul, norm_mul, norm_star]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le_torusSobolevWeight j k)
          (norm_nonneg _)) (norm_nonneg _)
  calc
    _ ≤ 2*(torusSobolevWeight k^(2*m) * (‖z‖*(torusSobolevWeight k*‖v‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ha (pow_nonneg (torusSobolevWeight_pos k).le _))
        (by norm_num)
    _ = 2*(torusSobolevWeight k^(m+1)*‖z‖)*(torusSobolevWeight k^m*‖v‖) := by
      rw [show 2*m=m+m by omega, pow_add, pow_succ]
      ring
    _ ≤ _ := scalar_young_div δ _ _ hδ

theorem weightedTransportPairing_abs_le_sum (m N : ℕ) (e q r : Phase N) :
    |weightedTransportPairing m N e q r| ≤
      ∑ k ∈ fullModes N, ∑ i : Fin 3, ∑ j : Fin 3,
        torusSobolevWeight k^(2*m) *
          |(star (phaseCoeff e k i) *
            (derivativeSymbol j k * fullTensorProduct N q r k i j)).re| := by
  unfold weightedTransportPairing
  calc
    _ ≤ ∑ k ∈ fullModes N, |torusSobolevWeight k^(2*m) *
        ∑ i : Fin 3, (star (phaseCoeff e k i) *
          fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _)]
      simp_rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (torusSobolevWeight_pos k).le _)
      calc
        _ ≤ ∑ i : Fin 3, |(star (phaseCoeff e k i) *
            fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i).re| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [fullBilinearTransport_eq_tensor_divergence, Finset.mul_sum, Complex.re_sum]
          exact Finset.abs_sum_le_sum_abs _ _

/-- A mixed native convection term can be absorbed by viscosity at every order. -/
theorem weightedTransportPairing_young (m N : ℕ) (e q r : Phase N)
    (δ : ℝ) (hδ : 0 < δ) :
    2*|weightedTransportPairing m N e q r| ≤
      3*δ*sobolevEnergy (m+1) N e +
      (18*((2:ℝ)^m)^2*latticeSobolevConstant/δ) *
        (sobolevEnergy 2 N r*sobolevEnergy m N q +
         sobolevEnergy 2 N q*sobolevEnergy m N r) := by
  have hterm (k : Frequency) (i j : Fin 3) :=
    weighted_triad_young m k j (phaseCoeff e k i) (fullTensorProduct N q r k i j) δ hδ
  have hsum := Finset.sum_le_sum (s := fullModes N) (fun k hk =>
    Finset.sum_le_sum (s := Finset.univ) (fun i hi =>
      Finset.sum_le_sum (s := Finset.univ) (fun j hj => hterm k i j)))
  have hstart := (mul_le_mul_of_nonneg_left
    (weightedTransportPairing_abs_le_sum m N e q r) (by norm_num : (0:ℝ)≤2)).trans
    (by simpa only [Finset.mul_sum] using hsum)
  have he : (∑ k ∈ fullModes N, ∑ i : Fin 3, ∑ j : Fin 3,
      δ*(torusSobolevWeight k^(m+1)*‖phaseCoeff e k i‖)^2) =
      3*δ*sobolevEnergy (m+1) N e := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [sobolevEnergy, sobolevEnergyDensity, sobolevWeightedCoeff_norm_eq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp : (∑ k ∈ fullModes N, ∑ i : Fin 3, ∑ j : Fin 3,
      (torusSobolevWeight k^m*‖fullTensorProduct N q r k i j‖)^2/δ) ≤
      (18*((2:ℝ)^m)^2*latticeSobolevConstant/δ) *
        (sobolevEnergy 2 N r*sobolevEnergy m N q +
         sobolevEnergy 2 N q*sobolevEnergy m N r) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := fullModes N) (t := Finset.univ)]
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          (2*((2:ℝ)^m)^2*latticeSobolevConstant *
            (sobolevEnergy 2 N r*sobolevEnergy m N q +
             sobolevEnergy 2 N q*sobolevEnergy m N r))/δ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right (fullTensorProduct_energy_bound m N q r i j) hδ.le
      _ = _ := by simp; ring
  simp only [Finset.sum_add_distrib] at hstart
  rw [he] at hstart
  exact hstart.trans (add_le_add le_rfl hp)

end
end QuantumAdapter.Obligations
