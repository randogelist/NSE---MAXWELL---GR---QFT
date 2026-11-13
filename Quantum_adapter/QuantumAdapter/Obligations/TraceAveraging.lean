import QuantumAdapter.Obligations.TraceTranslation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Exact translation averaging on the native full phase. Every continuous real
linear functional invariant under translations factors through the mean.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

theorem continuous_phaseTranslation_space (N : ℕ) (q : Phase N) :
    Continuous (fun x : Vec => phaseTranslation N x q) := by
  apply Continuous.subtype_mk
  apply (continuous_piLp 2).2
  intro ki
  exact (fourierCharacter_contDiff ki.1.val).continuous.mul continuous_const

theorem integrableOn_phaseTranslation_space (N : ℕ) (q : Phase N) :
    IntegrableOn (fun x : Vec => phaseTranslation N x q) unitCube volume :=
  (continuous_phaseTranslation_space N q).continuousOn.integrableOn_compact
    isCompact_unitCube

theorem phaseCoeff_zero_real (N : ℕ) (q : Phase N) (i : Fin 3) :
    ((phaseCoeff q 0 i).re : ℂ) = phaseCoeff q 0 i := by
  have hr := phaseCoeff_reality q 0 i
  simp only [neg_zero] at hr
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im hr
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem integral_phaseTranslation_space (N : ℕ) (q : Phase N) :
    (∫ x in unitCube, phaseTranslation N x q) = meanPhase N (meanVector q) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (∫ x in unitCube, phaseTranslation N x q) k i =
    phaseCoeff (meanPhase N (meanVector q)) k i
  have hc := (phaseCoordinate N k i).integral_comp_comm
    (integrableOn_phaseTranslation_space N q)
  simp only [phaseCoordinate_apply, phaseTranslation_coeff] at hc
  rw [← hc, integral_mul_const, integral_fourierCharacter, meanPhase_coeff]
  by_cases hk : k = 0
  · subst k
    simp only [if_pos rfl, one_mul]
    change phaseCoeff q 0 i = ((phaseCoeff q 0 i).re : ℂ)
    exact (phaseCoeff_zero_real N q i).symm
  · simp [hk]

theorem integral_unitCube_real_one :
    (∫ _x in unitCube, (1 : ℝ)) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa [fourierCharacter] using integral_fourierCharacter (0 : Frequency)

theorem integral_unitCube_real_const (a : ℝ) :
    (∫ _x in unitCube, a) = a := by
  calc
    _ = a * (∫ _x in unitCube, (1 : ℝ)) := by
      rw [← integral_const_mul]
      simp only [mul_one]
    _ = a := by rw [integral_unitCube_real_one, mul_one]

theorem translationInvariant_linear_eq_mean (N : ℕ)
    (l : Phase N →L[ℝ] ℝ)
    (hl : ∀ (x : Vec) (q : Phase N), l (phaseTranslation N x q) = l q)
    (q : Phase N) : l q = l (meanPhase N (meanVector q)) := by
  have h := l.integral_comp_comm (integrableOn_phaseTranslation_space N q)
  rw [integral_phaseTranslation_space] at h
  have hf : (fun x : Vec => l (phaseTranslation N x q)) = fun _ => l q := by
    funext x
    exact hl x q
  rw [hf, integral_unitCube_real_const] at h
  exact h

end
end QuantumAdapter.Obligations
