import SingularClosure.LerayPressure
import SingularClosure.GalerkinReality
import SingularClosure.FiniteParseval

/-!
# Contraction of the actual Leray projection

The orthogonal decomposition is derived from the literal modewise projection
formula and its proved solenoidal pairing identity. No orthogonality premise
is supplied to any contraction theorem below.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem complex_normSq_split (z w : ℂ) :
    Complex.normSq z = Complex.normSq w + Complex.normSq (z - w) +
      2 * (star w * (z - w)).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The actual longitudinal remainder is orthogonal to the actual Leray image. -/
theorem coefficientLeray_remainder_orthogonal (k : Frequency) (v : Fin 3 → ℂ) :
    (∑ i : Fin 3, star (coefficientLeray k v i) *
      (v i - coefficientLeray k v i)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr
    (coefficientLeray_pairing k (coefficientLeray k v) v
      (coefficientLeray_solenoidal k v)).symm

/-- Modewise Pythagoras for the literal Leray operator, including frequency zero. -/
theorem coefficientLeray_energy_pythagoras (k : Frequency) (v : Fin 3 → ℂ) :
    (∑ i : Fin 3, Complex.normSq (v i)) =
      (∑ i : Fin 3, Complex.normSq (coefficientLeray k v i)) +
      ∑ i : Fin 3, Complex.normSq (v i - coefficientLeray k v i) := by
  have horth : (∑ i : Fin 3,
      (star (coefficientLeray k v i) * (v i - coefficientLeray k v i)).re) = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using
      congrArg Complex.re (coefficientLeray_remainder_orthogonal k v)
  calc
    _ = ∑ i : Fin 3,
        (Complex.normSq (coefficientLeray k v i) +
          Complex.normSq (v i - coefficientLeray k v i) +
          2 * (star (coefficientLeray k v i) *
            (v i - coefficientLeray k v i)).re) := by
      apply Finset.sum_congr rfl
      intro i _
      exact complex_normSq_split (v i) (coefficientLeray k v i)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, horth, mul_zero, add_zero]

theorem coefficientLeray_energy_le (k : Frequency) (v : Fin 3 → ℂ) :
    (∑ i : Fin 3, Complex.normSq (coefficientLeray k v i)) ≤
      ∑ i : Fin 3, Complex.normSq (v i) := by
  rw [coefficientLeray_energy_pythagoras k v]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.normSq_eq_norm_sq]
  exact sq_nonneg _

def lerayFourierCoeff (c : FourierCoeff) : FourierCoeff :=
  fun k => coefficientLeray k (c k)

theorem lerayFourierCoeff_solenoidal (c : FourierCoeff) :
    SpectralSolenoidal (lerayFourierCoeff c) := by
  intro k
  exact coefficientLeray_solenoidal k (c k)

theorem lerayFourierCoeff_reality (c : FourierCoeff) (hc : SpectralReality c) :
    SpectralReality (lerayFourierCoeff c) := by
  intro k i
  have he : c (-k) = (fun j => star (c k j)) := by
    funext j
    exact hc k j
  change coefficientLeray (-k) (c (-k)) i = star (coefficientLeray k (c k) i)
  rw [he, coefficientLeray_neg_star]

/-- Every finite cutoff inherits the exact coefficient energy contraction. -/
theorem coefficientEnergy_leray_le (N : ℕ) (c : FourierCoeff) :
    coefficientEnergy N (lerayFourierCoeff c) ≤ coefficientEnergy N c := by
  unfold coefficientEnergy lerayFourierCoeff
  apply Finset.sum_le_sum
  intro k _
  exact coefficientLeray_energy_le k (c k)

theorem coefficientWeightedEnergy_leray_le (N : ℕ) (c : FourierCoeff)
    (w : Frequency → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (∑ k ∈ cutoffModes N, w k *
      (∑ i : Fin 3, Complex.normSq (lerayFourierCoeff c k i))) ≤
      ∑ k ∈ cutoffModes N, w k * (∑ i : Fin 3, Complex.normSq (c k i)) := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (coefficientLeray_energy_le k (c k)) (hw k)

/-- Literal physical energy contraction for a real Fourier family. -/
theorem physicalEnergy_leray_le (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) :
    physicalEnergy (finiteSynthesis N (lerayFourierCoeff c)) ≤
      physicalEnergy (finiteSynthesis N c) := by
  rw [FINITE_PHYSICAL_ENERGY_PARSEVAL N (lerayFourierCoeff c)
    (lerayFourierCoeff_reality c hc), FINITE_PHYSICAL_ENERGY_PARSEVAL N c hc]
  exact coefficientEnergy_leray_le N c

theorem integral_norm_sq_leray_le (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) :
    (∫ x in unitCube, ‖finiteSynthesis N (lerayFourierCoeff c) x‖ ^ 2) ≤
      ∫ x in unitCube, ‖finiteSynthesis N c x‖ ^ 2 := by
  simpa only [physicalEnergy_eq_integral_norm_sq] using physicalEnergy_leray_le N c hc

end

end SingularClosure
