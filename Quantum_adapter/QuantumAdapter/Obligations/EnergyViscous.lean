import QuantumAdapter.Obligations.EnergyOrdered
import QuantumAdapter.Obligations.TraceLaplacian

/-! Nonnegative viscosity in the exact ordered H3 polarization. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem phaseDerivative_laplacian (N : ℕ) (i : Fin 3) (q : Phase N) :
    phaseDerivative N i (phaseLaplacian N q) =
      phaseLaplacian N (phaseDerivative N i q) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  change phaseCoeff (phaseDerivative N i (phaseLaplacian N q)) =
    phaseCoeff (phaseLaplacian N (phaseDerivative N i q))
  funext k j
  simp only [phaseCoeff_phaseDerivative, phaseLaplacian_coeff, spectralMultiplier]
  ring

theorem inner_phaseLaplacian (N : ℕ) (q : Phase N) :
    inner ℝ q (phaseLaplacian N q) = dissipation N q := by
  rw [phase_inner_eq_sum]
  unfold dissipation
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [phaseLaplacian_coeff]
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.normSq_apply]
  ring

theorem orderedPairing_laplacian_nonneg (m N : ℕ) (q : Phase N) :
    0 ≤ orderedPairing m N q (phaseLaplacian N q) := by
  induction m generalizing q with
  | zero =>
    change 0 ≤ inner ℝ q (phaseLaplacian N q)
    rw [inner_phaseLaplacian]
    exact dissipation_nonneg N q
  | succ m ih =>
    simp only [orderedPairing, phaseDerivative_laplacian]
    exact Finset.sum_nonneg (fun i hi => ih _)

theorem h3Pairing_laplacian_nonneg (N : ℕ) (q : Phase N) :
    0 ≤ h3Pairing N q (phaseLaplacian N q) := by
  have h0 := orderedPairing_laplacian_nonneg 0 N q
  have h1 := orderedPairing_laplacian_nonneg 1 N q
  have h2 := orderedPairing_laplacian_nonneg 2 N q
  have h3 := orderedPairing_laplacian_nonneg 3 N q
  unfold h3Pairing
  positivity

theorem h3Pairing_add_right (N : ℕ) (q a b : Phase N) :
    h3Pairing N q (a + b) = h3Pairing N q a + h3Pairing N q b := by
  simp only [h3Pairing, orderedPairing_add_right]
  ring

theorem h3Pairing_smul_right (N : ℕ) (q a : Phase N) (s : ℝ) :
    h3Pairing N q (s • a) = s * h3Pairing N q a := by
  simp only [h3Pairing, orderedPairing_smul_right]
  ring

end
end QuantumAdapter.Obligations
