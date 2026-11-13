import SingularClosure.GalerkinAlgebra

/-!
# Concrete Leray and pressure coefficient identities

The denominator is proved nonzero for every nonzero integer frequency.
The actual modewise Leray projection preserves the solenoidal constraint.
The pressure coefficient below recovers the longitudinal correction at each
nonzero mode. Infinite Fourier convergence, smooth pressure reconstruction,
and the physical pressure endpoint remain separate analytic obligations.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem galerkinFreqSq_nonneg (k : Frequency) : 0 ≤ galerkinFreqSq k := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (k i))

theorem frequency_complex_square_sum_ne_zero (k : Frequency) (hk : k ≠ 0) :
    (∑ i : Fin 3, (k i : ℂ) ^ 2) ≠ 0 := by
  have hr : (∑ i : Fin 3, (k i : ℝ) ^ 2) ≠ 0 := by
    intro heq
    simp [Fin.sum_univ_succ] at heq
    have h0 : (k 0 : ℝ) = 0 := by
      nlinarith [sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
    have h1 : (k 1 : ℝ) = 0 := by
      nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
    have h2 : (k 2 : ℝ) = 0 := by
      nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
    apply hk
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1
    · exact_mod_cast h2
  intro hc
  apply hr
  exact_mod_cast hc

/-- Leray projection has exactly zero Fourier divergence. -/
theorem coefficientLeray_solenoidal (k : Frequency) (v : Fin 3 → ℂ) :
    (∑ i : Fin 3, (k i : ℂ) * coefficientLeray k v i) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hden := frequency_complex_square_sum_ne_zero k hk
    simp only [coefficientLeray, hk, if_false, mul_sub, Finset.sum_sub_distrib]
    have hterm (i : Fin 3) :
        (k i : ℂ) * ((k i : ℂ) * (∑ j : Fin 3, (k j : ℂ) * v j) /
          (∑ j : Fin 3, (k j : ℂ) ^ 2)) =
        (k i : ℂ) ^ 2 * (∑ j : Fin 3, (k j : ℂ) * v j) /
          (∑ j : Fin 3, (k j : ℂ) ^ 2) := by ring
    simp_rw [hterm]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    ring

theorem coefficientLeray_eq_of_solenoidal (k : Frequency) (v : Fin 3 → ℂ)
    (hv : (∑ i : Fin 3, (k i : ℂ) * v i) = 0) :
    coefficientLeray k v = v := by
  funext i
  by_cases hk : k = 0 <;> simp [coefficientLeray, hk, hv]

theorem coefficientLeray_idempotent (k : Frequency) (v : Fin 3 → ℂ) :
    coefficientLeray k (coefficientLeray k v) = coefficientLeray k v := by
  exact coefficientLeray_eq_of_solenoidal k _ (coefficientLeray_solenoidal k v)

/-- The concrete coefficient vector field is tangent to the solenoidal space. -/
theorem galerkinRhs_solenoidal (ν : ℝ) (N : ℕ) (c : FourierCoeff)
    (hc : SpectralSolenoidal c) (k : Frequency) :
    (∑ i : Fin 3, (k i : ℂ) * galerkinRhs ν N c k i) = 0 := by
  have hpoint (i : Fin 3) :
      (k i : ℂ) *
        (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c k i) =
      -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
        ((k i : ℂ) * c k i) := by ring
  simp only [galerkinRhs, mul_sub, Finset.sum_sub_distrib, hpoint,
    ← Finset.mul_sum, hc k, coefficientLeray_solenoidal, mul_zero, sub_zero]

/-- Pressure Fourier coefficient for a prescribed convection coefficient. -/
def pressureFromTransport (k : Frequency) (v : Fin 3 → ℂ) : ℂ :=
  if k = 0 then 0 else
    Complex.I * (∑ j : Fin 3, (k j : ℂ) * v j) /
      (((2 * Real.pi : ℝ) : ℂ) * (∑ j : Fin 3, (k j : ℂ) ^ 2))

/-- Recovery of the longitudinal pressure term, with the literal Fourier sign. -/
theorem pressureFromTransport_recovery (k : Frequency) (v : Fin 3 → ℂ)
    (i : Fin 3) :
    v i + (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k i : ℂ)) *
      pressureFromTransport k v = coefficientLeray k v i := by
  by_cases hk : k = 0
  · simp [pressureFromTransport, coefficientLeray, hk]
  · have hd := frequency_complex_square_sum_ne_zero k hk
    have hp : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
    simp only [pressureFromTransport, coefficientLeray, hk, if_false]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring

end

end SingularClosure
