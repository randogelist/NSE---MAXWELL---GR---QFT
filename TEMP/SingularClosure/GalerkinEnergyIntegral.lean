import SingularClosure.GalerkinEnergy

/-!
# Integrated energy identity for actual Galerkin trajectories

The dissipation is continuous and integrable on every finite forward interval.
The equality below follows from the concrete ODE energy derivative and the
fundamental theorem of calculus. Physical Parseval identification is separate.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem GalerkinSolution.coefficientEnergy_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => coefficientEnergy N (g.coeff t)) (Ici 0) := by
  intro t ht
  exact (g.coefficientEnergy_identity ht).continuousWithinAt

theorem GalerkinSolution.coefficientDissipation_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => coefficientDissipation N (g.coeff t)) (Ici 0) := by
  unfold coefficientDissipation
  apply continuousOn_finset_sum
  intro k hk
  apply continuousOn_finset_sum
  intro i hi
  simp_rw [Complex.normSq_eq_norm_sq]
  exact continuousOn_const.mul ((g.coefficient_continuous k i).norm.pow 2)

theorem GalerkinSolution.coefficientDissipation_intervalIntegrable
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => coefficientDissipation N (g.coeff t)) volume 0 T := by
  exact (g.coefficientDissipation_continuousOn.mono
    (fun t ht => ht.1)).intervalIntegrable_of_Icc hT

/-- Exact energy plus accumulated dissipation on any finite forward interval. -/
theorem GalerkinSolution.coefficientEnergy_integral_identity
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T) :
    coefficientEnergy N (g.coeff T) +
      2 * ν * (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t)) =
        coefficientEnergy N (g.coeff 0) := by
  have hE : ContinuousOn (fun t => coefficientEnergy N (g.coeff t)) (Icc 0 T) :=
    g.coefficientEnergy_continuousOn.mono (fun t ht => ht.1)
  have hD : IntervalIntegrable
      (fun t => (-2 * ν) * coefficientDissipation N (g.coeff t)) volume 0 T :=
    (g.coefficientDissipation_intervalIntegrable hT).const_mul (-2 * ν)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s => coefficientEnergy N (g.coeff s))
        ((-2 * ν) * coefficientDissipation N (g.coeff t)) t := by
    intro t ht
    exact (g.coefficientEnergy_identity ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE hderiv hD
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

/-- The initial coefficient energy is precisely the cutoff energy of the datum. -/
theorem GalerkinSolution.coefficientEnergy_initial_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    coefficientEnergy N (g.coeff 0) = coefficientEnergy N (datumFourierCoeff a) := by
  unfold coefficientEnergy
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [g.initial k i, if_pos hk]

/-- The exact finite-time dissipation bound; no square-enstrophy premise is used. -/
theorem GalerkinSolution.coefficientDissipation_integral_le
    {ν : ℝ} (hν : 0 < ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t)) ≤
      coefficientEnergy N (datumFourierCoeff a) / (2 * ν) := by
  rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hν)]
  have hE := g.coefficientEnergy_integral_identity hT
  rw [g.coefficientEnergy_initial_eq] at hE
  have hnonneg := coefficientEnergy_nonneg N (g.coeff T)
  nlinarith

end

end SingularClosure
