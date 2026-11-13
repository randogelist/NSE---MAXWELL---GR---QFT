import QuantumAdapter.Obligations.TraceTranslation

/-! Translation conjugacy of the actual native drift and its real divergence. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure QuantumAdapter.Assembly

theorem fourierCharacter_convolution_split (k p : Frequency) (x : Vec) :
    fourierCharacter p x * fourierCharacter (k - p) x = fourierCharacter k x := by
  rw [fourierCharacter_mul]
  congr 1
  abel

theorem fullTransport_phaseTranslation (N : ℕ) (x : Vec) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    fullTransport N (phaseCoeff (phaseTranslation N x q)) k i =
      fourierCharacter k x * fullTransport N (phaseCoeff q) k i := by
  classical
  simp only [fullTransport, phaseTranslation_coeff]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hinner :
      (∑ j : Fin 3, (fourierCharacter p x * phaseCoeff q p j) *
        (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
      fourierCharacter p x *
        (∑ j : Fin 3, phaseCoeff q p j *
          (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hinner]
  calc
    _ = (fourierCharacter p x * fourierCharacter (k - p) x) *
        ((∑ j : Fin 3, phaseCoeff q p j *
          (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) *
            phaseCoeff q (k - p) i) := by ring
    _ = _ := by rw [fourierCharacter_convolution_split]

theorem coefficientLeray_complex_mul (k : Frequency) (a : ℂ)
    (v : Fin 3 → ℂ) (i : Fin 3) :
    coefficientLeray k (fun j => a * v j) i = a * coefficientLeray k v i := by
  classical
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, if_neg hk]
    have hs : (∑ j : Fin 3, (k j : ℂ) * (a * v j)) =
        a * ∑ j : Fin 3, (k j : ℂ) * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hs]
    ring

theorem drift_coeff_formula (ν : ℝ) (N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    phaseCoeff (drift ν N q) k i =
      if k ∈ fullModes N then
        if k = 0 then 0 else
          -((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff q k i -
            coefficientLeray k (fullTransport N (phaseCoeff q) k) i
      else 0 := by
  change extendCoeff (drift ν N q).val k i = _
  rw [drift_eq_rawRhs]
  exact rawRhs_coeff ν N q k i

theorem drift_phaseTranslation (ν : ℝ) (N : ℕ) (x : Vec) (q : Phase N) :
    drift ν N (phaseTranslation N x q) = phaseTranslation N x (drift ν N q) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (drift ν N (phaseTranslation N x q)) k i =
    phaseCoeff (phaseTranslation N x (drift ν N q)) k i
  rw [phaseTranslation_coeff, drift_coeff_formula, drift_coeff_formula]
  by_cases hk : k ∈ fullModes N
  · rw [if_pos hk, if_pos hk]
    by_cases hzero : k = 0
    · simp [hzero]
    · rw [if_neg hzero, if_neg hzero, phaseTranslation_coeff]
      have ht : fullTransport N (phaseCoeff (phaseTranslation N x q)) k =
          fun j => fourierCharacter k x * fullTransport N (phaseCoeff q) k j := by
        funext j
        exact fullTransport_phaseTranslation N x q k j
      rw [ht, coefficientLeray_complex_mul]
      ring
  · simp [hk]

theorem drift_fderiv_phaseTranslation (ν : ℝ) (N : ℕ) (x : Vec) (q : Phase N) :
    (fderiv ℝ (drift ν N) (phaseTranslation N x q)).comp
        (phaseTranslationCLE N x).toContinuousLinearMap =
      (phaseTranslationCLE N x).toContinuousLinearMap.comp
        (fderiv ℝ (drift ν N) q) := by
  let T := phaseTranslationCLE N x
  have hd := (contDiff_drift ν N).differentiable (by simp)
  have hleft := (hd (T q)).hasFDerivAt.comp q T.hasFDerivAt
  have hright := T.hasFDerivAt.comp q (hd q).hasFDerivAt
  have heq : (fun z : Phase N => drift ν N (T z)) =
      (fun z : Phase N => T (drift ν N z)) := by
    funext z
    exact drift_phaseTranslation ν N x z
  change HasFDerivAt (fun z : Phase N => drift ν N (T z))
      ((fderiv ℝ (drift ν N) (T q)).comp T.toContinuousLinearMap) q at hleft
  rw [heq] at hleft
  exact hleft.unique hright

theorem driftDivergence_phaseTranslation (ν : ℝ) (N : ℕ) (x : Vec) (q : Phase N) :
    driftDivergence ν N (phaseTranslation N x q) = driftDivergence ν N q := by
  let T := phaseTranslationCLE N x
  rw [driftDivergence_eq_linearTrace, driftDivergence_eq_linearTrace]
  have hd := drift_fderiv_phaseTranslation ν N x q
  have hconj : (fderiv ℝ (drift ν N) (phaseTranslation N x q)).toLinearMap =
      T.toLinearEquiv.conj (fderiv ℝ (drift ν N) q).toLinearMap := by
    apply LinearMap.ext
    intro r
    have hh := congrArg (fun A : Phase N →L[ℝ] Phase N => A (T.symm r)) hd
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe, T,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using hh
  rw [hconj]
  exact LinearMap.trace_conj' _ _

end
end QuantumAdapter.Obligations
