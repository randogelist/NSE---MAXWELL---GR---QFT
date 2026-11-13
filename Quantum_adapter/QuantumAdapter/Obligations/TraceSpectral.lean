import QuantumAdapter.Obligations.TraceAmbient

/-! Exact real spectral multiplicity of the native constrained Laplacian. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure QuantumAdapter.Assembly

theorem ambientSingle_coeff (N : ℕ) (ki : PhaseIndex N) (z : ℂ)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (ambientSingle N ki z) k i =
      if k = ki.1.val ∧ i = ki.2 then z else 0 := by
  classical
  by_cases hk : k ∈ fullModes N
  · simp [extendCoeff, hk, ambientSingle_apply, Prod.ext_iff, Subtype.ext_iff]
  · have hne : k ≠ ki.1.val := by
      intro h
      apply hk
      rw [h]
      exact ki.1.property
    simp [extendCoeff, hk, hne]

theorem frequency_neg_ne_self {k : Frequency} (hk : k ≠ 0) : -k ≠ k := by
  intro h
  apply hk
  funext i
  have hi := congrFun h i
  change -(k i) = k i at hi
  change k i = 0
  omega

theorem realityAverage_single_at_mode (N : ℕ) (ki : PhaseIndex N) (z : ℂ)
    (hk : ki.1.val ≠ 0) :
    realityAverage N (ambientSingle N ki z) ki.1.val = Pi.single ki.2 (z / 2) := by
  funext j
  simp only [realityAverage, ambientSingle_coeff]
  have hn := frequency_neg_ne_self hk
  simp [hn, Pi.single_apply]

theorem frequencySquare_complex_eq_real (k : Frequency) :
    (∑ j : Fin 3, (k j : ℂ) ^ 2) = ((galerkinFreqSq k : ℝ) : ℂ) := by
  simp [galerkinFreqSq]

theorem coefficientLeray_single_diagonal (k : Frequency) (hk : k ≠ 0)
    (i : Fin 3) (z : ℂ) :
    coefficientLeray k (Pi.single i (z / 2)) i =
      (((1 - (k i : ℝ) ^ 2 / (galerkinFreqSq k : ℝ)) / 2 : ℝ) : ℂ) * z := by
  classical
  simp only [coefficientLeray, if_neg hk]
  simp only [Pi.single_apply, ite_true]
  have hs : (∑ j : Fin 3, (k j : ℂ) * if j = i then z / 2 else 0) =
      (k i : ℂ) * (z / 2) := by
    simp
  rw [hs, frequencySquare_complex_eq_real]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  ring

def ambientLaplacianRetraction (N : ℕ) : AmbientPhase N →ₗ[ℝ] AmbientPhase N :=
  (phaseSubmodule N).subtype.comp ((phaseLaplacian N).comp (phaseRetraction N))

theorem ambientLaplacianRetraction_single_diagonal (N : ℕ)
    (ki : PhaseIndex N) (z : ℂ) (hk : ki.1.val ≠ 0) :
    ambientLaplacianRetraction N (ambientSingle N ki z) ki =
      ((laplaceSymbol ki.1.val *
        ((1 - (ki.1.val ki.2 : ℝ) ^ 2 / (galerkinFreqSq ki.1.val : ℝ)) / 2) : ℝ) : ℂ) * z := by
  change (phaseLaplacian N (phaseRetraction N (ambientSingle N ki z))).val ki = _
  rw [← phaseCoeff_mode N _ ki, phaseLaplacian_coeff, phaseRetraction_coeff,
    realityAverage_single_at_mode N ki z hk, coefficientLeray_single_diagonal _ hk]
  simp only [Complex.ofReal_mul]
  ring

theorem ambientLaplacianRetraction_single_diagonal_zero (N : ℕ)
    (ki : PhaseIndex N) (z : ℂ) (hk : ki.1.val = 0) :
    ambientLaplacianRetraction N (ambientSingle N ki z) ki = 0 := by
  change (phaseLaplacian N (phaseRetraction N (ambientSingle N ki z))).val ki = 0
  rw [← phaseCoeff_mode N _ ki, phaseLaplacian_coeff, hk, laplaceSymbol_zero_native]
  simp

theorem ambientLaplacianRetraction_real_diagonal (N : ℕ) (ki : PhaseIndex N) :
    (ambientLaplacianRetraction N (ambientSingle N ki 1) ki).re +
      (ambientLaplacianRetraction N (ambientSingle N ki Complex.I) ki).im =
      laplaceSymbol ki.1.val *
        (1 - (ki.1.val ki.2 : ℝ) ^ 2 / (galerkinFreqSq ki.1.val : ℝ)) := by
  by_cases hk : ki.1.val = 0
  · rw [ambientLaplacianRetraction_single_diagonal_zero N ki 1 hk,
      ambientLaplacianRetraction_single_diagonal_zero N ki Complex.I hk]
    simp [hk]
  · rw [ambientLaplacianRetraction_single_diagonal N ki 1 hk,
      ambientLaplacianRetraction_single_diagonal N ki Complex.I hk]
    simp only [mul_one, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero]
    ring

theorem leray_diagonal_sum (k : Frequency) (hk : k ≠ 0) :
    (∑ i : Fin 3, (1 - (k i : ℝ) ^ 2 / (galerkinFreqSq k : ℝ))) = 2 := by
  have hc := frequencySquare_ne_zero k hk
  rw [frequencySquare_complex_eq_real] at hc
  have hd : (galerkinFreqSq k : ℝ) ≠ 0 := by
    intro h
    apply hc
    rw [h]
    simp
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  have hs : (∑ i : Fin 3, (k i : ℝ) ^ 2) = (galerkinFreqSq k : ℝ) := by
    simp [galerkinFreqSq]
  rw [hs, div_self hd]
  norm_num

theorem phaseLaplacian_trace (N : ℕ) :
    LinearMap.trace ℝ (Phase N) (phaseLaplacian N) = finiteLaplaceTrace N := by
  rw [phaseLaplacian_trace_eq_ambient]
  change LinearMap.trace ℝ (AmbientPhase N) (ambientLaplacianRetraction N) = _
  rw [ambient_real_trace_formula]
  simp_rw [ambientLaplacianRetraction_real_diagonal]
  rw [← sum_fullModes_eq_sum_coordinates]
  unfold finiteLaplaceTrace
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : k = 0
  · subst k
    simp
  · rw [← Finset.mul_sum, leray_diagonal_sum k hz]
    ring

/-- Exact P1 for the native full real Fourier phase and every real viscosity. -/
theorem native_drift_divergence (ν : ℝ) (N : ℕ) (q : Phase N) :
    driftDivergence ν N q = -phaseDecayRate ν N := by
  rw [driftDivergence_eq_neg_viscosity_mul_trace, phaseLaplacian_trace]
  simp [phaseDecayRate]

end
end QuantumAdapter.Obligations
