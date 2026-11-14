import SingularClosure.PhysicalEnergy
import SingularClosure.EnstrophyInequality

/-!
# Cutoff-independent periodic Poincare estimates

Every frequency retained by the concrete Galerkin cutoff is a nonzero integer
vector. Its squared length is therefore at least one. Finite Parseval transfers
the resulting coefficient inequality to the literal physical energy and
gradient integrals on the unit cube, with constant `4 * pi^2` independent of
the cutoff, viscosity, and datum.

These are auxiliary estimates for endpoint 5. No nonlinear Sobolev estimate is
asserted or assumed here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem galerkinFreqSq_ge_one_of_ne_zero (k : Frequency) (hk : k ≠ 0) :
    (1 : ℤ) ≤ galerkinFreqSq k := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  have hpos : (0 : ℤ) < (k i) ^ 2 := sq_pos_of_ne_zero hi
  have hsum : (k i) ^ 2 ≤ ∑ j : Fin 3, (k j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i)
  change (1 : ℤ) ≤ ∑ j : Fin 3, (k j) ^ 2
  omega

theorem galerkinFreqSq_ge_one_of_mem {N : ℕ} {k : Frequency}
    (hk : k ∈ cutoffModes N) : (1 : ℤ) ≤ galerkinFreqSq k := by
  exact galerkinFreqSq_ge_one_of_ne_zero k
    ((mem_cutoffModes_iff N k).mp hk).2.1

theorem fourierLaplacianSymbol_ge_four_pi_sq {N : ℕ} {k : Frequency}
    (hk : k ∈ cutoffModes N) :
    4 * Real.pi ^ 2 ≤ (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) := by
  have hfreq : (1 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_ge_one_of_mem hk
  calc
    4 * Real.pi ^ 2 = (2 * Real.pi) ^ 2 * 1 := by ring
    _ ≤ (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) :=
      mul_le_mul_of_nonneg_left hfreq (sq_nonneg _)

/-- Sharp unit-period Poincare constant for every finite coefficient family. -/
theorem COEFFICIENT_POINCARE (N : ℕ) (c : FourierCoeff) :
    4 * Real.pi ^ 2 * coefficientEnergy N c ≤ coefficientDissipation N c := by
  simp only [coefficientEnergy, coefficientDissipation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right (fourierLaplacianSymbol_ge_four_pi_sq hk)
  rw [Complex.normSq_eq_norm_sq]
  exact sq_nonneg _

/-- The same spectral gap controls the gradient energy by the Laplacian energy. -/
theorem COEFFICIENT_GRADIENT_POINCARE (N : ℕ) (c : FourierCoeff) :
    4 * Real.pi ^ 2 * coefficientDissipation N c ≤ coefficientLaplacianSquare N c := by
  simp only [coefficientDissipation, coefficientLaplacianSquare, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  have hgap := fourierLaplacianSymbol_ge_four_pi_sq hk
  have hfreqNonneg : 0 ≤ (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) := by
    exact (mul_nonneg (by norm_num) (sq_nonneg Real.pi)).trans hgap
  have hnorm : 0 ≤ Complex.normSq (c k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hgap hfreqNonneg) hnorm
  nlinarith only [hmul]

/-- Literal physical Poincare inequality for finite real Fourier synthesis. -/
theorem FINITE_PHYSICAL_POINCARE (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    4 * Real.pi ^ 2 * physicalEnergy (finiteSynthesis N c) ≤
      physicalDissipation (finiteSynthesis N c) := by
  rw [FINITE_PHYSICAL_ENERGY_PARSEVAL N c hreal]
  change 4 * Real.pi ^ 2 * coefficientEnergy N c ≤
    ∫ x in unitCube, gradientSquareDensity (finiteSynthesis N c) x
  rw [FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal]
  exact COEFFICIENT_POINCARE N c

/-- Poincare directly in physical norm notation, on the normalized unit cube. -/
theorem FINITE_PHYSICAL_NORM_POINCARE (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    4 * Real.pi ^ 2 * (∫ x in unitCube, ‖finiteSynthesis N c x‖ ^ 2) ≤
      ∫ x in unitCube,
        ∑ i : Fin 3, ‖coordinateDerivative (finiteSynthesis N c) i x‖ ^ 2 := by
  have h := FINITE_PHYSICAL_POINCARE N c hreal
  simpa only [physicalEnergy_eq_integral_norm_sq, physicalDissipation,
    gradientSquareDensity_eq_sum_norm_sq] using h

/-- Actual Galerkin trajectories satisfy the physical spectral-gap estimate. -/
theorem GalerkinSolution.physicalPoincare
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    4 * Real.pi ^ 2 * physicalEnergy (g.velocity t) ≤
      physicalDissipation (g.velocity t) :=
  FINITE_PHYSICAL_POINCARE N (g.coeff t) (g.real_symmetry t ht)

end

end SingularClosure
