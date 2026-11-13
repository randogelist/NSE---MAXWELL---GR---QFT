import SingularClosure.GalerkinEnergy

/-!
# Exact coefficient enstrophy evolution

This module proves the differentiated, viscosity-separated enstrophy identity
for the actual Fourier--Galerkin trajectories.  It does not assert the frozen
cutoff-independent enstrophy inequality.  Its remaining nonlinear term is the
literal weighted Fourier convolution pairing; no estimate for that term is
assumed or installed as a new axiom.

Physical Parseval identification and the periodic Sobolev/Gagliardo--Nirenberg
estimate are separate obligations.  The latter must produce a constant
independent of the cutoff before endpoint 5 can be completed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators

namespace SingularClosure

noncomputable section

/-- The Fourier square of the physical Laplacian norm, before Parseval. -/
def coefficientLaplacianSquare (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ 2 *
      Complex.normSq (c k i)

/-- The actual nonlinear enstrophy pairing, including the Leray projection. -/
def coefficientEnstrophyNonlinearPower (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
      (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re

theorem coefficientLaplacianSquare_nonneg (N : ℕ) (c : FourierCoeff) :
    0 ≤ coefficientLaplacianSquare N c := by
  unfold coefficientLaplacianSquare
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Differentiation of the concrete finite enstrophy sum. -/
theorem GalerkinSolution.coefficientDissipation_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r))
      (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
          (2 * (star (g.coeff t k i) * galerkinRhs ν N (g.coeff t) k i).re))
      (Ici 0) t := by
  unfold coefficientDissipation
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.fun_sum
  intro i hi
  exact (hasDerivWithinAt_complex_normSq (g.equation t ht k hk i)).const_mul _

/-- Algebraic viscosity splitting for the exact enstrophy derivative. -/
theorem coefficientDissipation_rate_split (ν : ℝ) (N : ℕ) (c : FourierCoeff) :
    (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
        (2 * (star (c k i) * galerkinRhs ν N c k i).re)) =
      (-2 * ν) * coefficientLaplacianSquare N c -
        2 * coefficientEnstrophyNonlinearPower N c := by
  have hpoint (k : Frequency) (i : Fin 3) :
      ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
        (2 * (star (c k i) * galerkinRhs ν N c k i).re) =
      (-2 * ν) *
        (((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ 2 *
          Complex.normSq (c k i)) -
        2 * (((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
          (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re) := by
    rw [galerkinRhs, complex_viscous_pairing]
    ring
  simp only [hpoint, coefficientLaplacianSquare, coefficientEnstrophyNonlinearPower,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Exact enstrophy balance, retaining the nonvanishing nonlinear pairing. -/
theorem GalerkinSolution.coefficientEnstrophy_identity
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r))
      ((-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
        2 * coefficientEnstrophyNonlinearPower N (g.coeff t)) (Ici 0) t := by
  rw [← coefficientDissipation_rate_split]
  exact g.coefficientDissipation_hasDerivWithinAt ht

/-- Pressure has zero contribution to the enstrophy pairing of a solenoidal state. -/
theorem coefficientEnstrophyNonlinearPower_eq_transport
    (N : ℕ) (c : FourierCoeff) (hc : SpectralSolenoidal c) :
    coefficientEnstrophyNonlinearPower N c =
      ∑ k ∈ cutoffModes N,
        ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
          (∑ i : Fin 3, star (c k i) * coefficientTransport N c k i).re := by
  unfold coefficientEnstrophyNonlinearPower
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.mul_sum, ← Complex.re_sum,
    coefficientLeray_pairing k (c k) (coefficientTransport N c k) (hc k)]

end

end SingularClosure
