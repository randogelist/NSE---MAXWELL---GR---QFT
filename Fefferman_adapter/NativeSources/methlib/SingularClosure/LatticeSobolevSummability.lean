import SingularClosure.TorusSobolev
import Mathlib.Algebra.Module.ZLattice.Summable

/-! Actual three-dimensional lattice summability and the uniform Fourier H² to ℓ¹ bound. -/

set_option autoImplicit false
set_option Elab.async true

open Set Module
open scoped BigOperators

namespace SingularClosure

noncomputable section

abbrev frequencyIntegerLattice : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

def frequencyLatticePoint (k : Frequency) : frequencyIntegerLattice :=
  ⟨fun i => (k i : ℝ), by
    apply ((Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨k i, by simp⟩⟩

theorem frequencyLatticePoint_injective : Function.Injective frequencyLatticePoint := by
  intro k l h
  funext i
  have hi := congrArg (fun z : frequencyIntegerLattice => (z : Fin 3 → ℝ) i) h
  change (k i : ℝ) = (l i : ℝ) at hi
  exact Int.cast_injective hi

theorem frequencyLatticePoint_zero : frequencyLatticePoint 0 = 0 := by
  ext i
  simp [frequencyLatticePoint]

theorem frequencyIntegerLattice_rank : Module.finrank ℤ frequencyIntegerLattice = 3 := by
  rw [ZLattice.rank ℝ frequencyIntegerLattice]
  simp

theorem summable_frequencyLatticePoint_inv_four :
    Summable (fun k : Frequency => ‖frequencyLatticePoint k‖⁻¹ ^ 4) := by
  have hlat := ZLattice.summable_norm_pow_inv frequencyIntegerLattice 4
    (by rw [frequencyIntegerLattice_rank]; norm_num)
  exact hlat.comp_injective frequencyLatticePoint_injective

theorem frequencyLatticePoint_norm_le_weight (k : Frequency) :
    ‖frequencyLatticePoint k‖ ≤ torusSobolevWeight k := by
  have hfreq : 0 ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hcoordinate (i : Fin 3) : |(k i : ℝ)| ≤ torusSobolevWeight k := by
    have hi : (k i : ℝ) ^ 2 ≤ (galerkinFreqSq k : ℝ) := by
      unfold galerkinFreqSq
      push_cast
      exact Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
    unfold torusSobolevWeight
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    rw [sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right hpi hfreq]
  change ‖(fun i : Fin 3 => (k i : ℝ))‖ ≤ torusSobolevWeight k
  apply (pi_norm_le_iff_of_nonneg (torusSobolevWeight_pos k).le).mpr
  intro i
  simpa only [Real.norm_eq_abs] using hcoordinate i

/-- The actual reciprocal fourth-power weight is summable on all integer frequencies. -/
theorem summable_torusSobolevWeight_inv_four :
    Summable (fun k : Frequency => (torusSobolevWeight k)⁻¹ ^ 4) := by
  classical
  have hdelta : Summable (fun k : Frequency => if k = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : Frequency) (1 : ℝ)).summable
  apply Summable.of_nonneg_of_le (fun k => by positivity) _
    (summable_frequencyLatticePoint_inv_four.add hdelta)
  intro k
  by_cases hk : k = 0
  · subst k
    simp [frequencyLatticePoint_zero, torusSobolevWeight, galerkinFreqSq]
  · simp only [if_neg hk, add_zero]
    have hp : frequencyLatticePoint k ≠ 0 := by
      intro h
      apply hk
      apply frequencyLatticePoint_injective
      exact h.trans frequencyLatticePoint_zero.symm
    have hnorm : 0 < ‖frequencyLatticePoint k‖ := norm_pos_iff.mpr hp
    have hinv : (torusSobolevWeight k)⁻¹ ≤ ‖frequencyLatticePoint k‖⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le hnorm (frequencyLatticePoint_norm_le_weight k)
    exact pow_le_pow_left₀ (inv_nonneg.mpr (torusSobolevWeight_pos k).le) hinv 4

def latticeSobolevConstant : ℝ :=
  1 + ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4

theorem latticeSobolevConstant_pos : 0 < latticeSobolevConstant := by
  have hsum : 0 ≤ ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4 :=
    tsum_nonneg (fun k => by positivity)
  unfold latticeSobolevConstant
  linarith

/-- The coefficient ℓ¹ norm is controlled by the actual H² Fourier weight,
with one constant independent of the finite support. -/
theorem finite_l1_sq_le_H2_sq (s : Finset Frequency) (a : Frequency → ℂ) :
    (∑ k ∈ s, ‖a k‖) ^ 2 ≤ latticeSobolevConstant *
      (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖a k‖) ^ 2) := by
  have hcancel (k : Frequency) :
      (torusSobolevWeight k)⁻¹ ^ 2 * (torusSobolevWeight k ^ 2 * ‖a k‖) = ‖a k‖ := by
    rw [inv_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 (torusSobolevWeight_pos k).ne'), one_mul]
  have hpower (k : Frequency) :
      ((torusSobolevWeight k)⁻¹ ^ 2) ^ 2 = (torusSobolevWeight k)⁻¹ ^ 4 := by ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun k => (torusSobolevWeight k)⁻¹ ^ 2)
    (fun k => torusSobolevWeight k ^ 2 * ‖a k‖)
  simp_rw [hcancel, hpower] at hCS
  have hsum : (∑ k ∈ s, (torusSobolevWeight k)⁻¹ ^ 4) ≤ latticeSobolevConstant := by
    have h := Summable.sum_le_tsum s (fun k _ => by positivity)
      summable_torusSobolevWeight_inv_four
    unfold latticeSobolevConstant
    linarith
  exact hCS.trans (mul_le_mul_of_nonneg_right hsum
    (Finset.sum_nonneg (fun k _ => sq_nonneg _)))

theorem FINITE_FOURIER_H2_L1_BOUND : ∃ C : ℝ, 0 < C ∧
    ∀ (s : Finset Frequency) (a : Frequency → ℂ),
      (∑ k ∈ s, ‖a k‖) ^ 2 ≤ C *
        (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖a k‖) ^ 2) :=
  ⟨latticeSobolevConstant, latticeSobolevConstant_pos, finite_l1_sq_le_H2_sq⟩

end

end SingularClosure
