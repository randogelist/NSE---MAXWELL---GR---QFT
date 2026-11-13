import QuantumAdapter.Assembly.Flow

/-!
The positive Laplacian and exact affine-viscosity drift decomposition.
This module is independent of every phase-divergence theorem.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure QuantumAdapter.Assembly

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

@[simp] theorem laplaceSymbol_neg_native (k : Frequency) :
    laplaceSymbol (-k) = laplaceSymbol k := by
  simp [laplaceSymbol, galerkinFreqSq]

@[simp] theorem laplaceSymbol_zero_native : laplaceSymbol 0 = 0 := by
  simp [laplaceSymbol, galerkinFreqSq]

def laplaceAmbient (N : ℕ) (q : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => (laplaceSymbol ki.1.val : ℂ) * phaseCoeff q ki.1.val ki.2)

theorem laplaceAmbient_coeff (N : ℕ) (q : Phase N) (k : Frequency) (i : Fin 3) :
    extendCoeff (laplaceAmbient N q) k i = (laplaceSymbol k : ℂ) * phaseCoeff q k i := by
  by_cases hk : k ∈ fullModes N
  · simp [laplaceAmbient, extendCoeff, hk]
  · simp [laplaceAmbient, extendCoeff, hk, phaseCoeff_support q k hk i]

theorem laplaceAmbient_mem (N : ℕ) (q : Phase N) :
    laplaceAmbient N q ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [laplaceAmbient_coeff, laplaceAmbient_coeff,
      laplaceSymbol_neg_native, phaseCoeff_reality q k i, star_mul]
    simp [mul_comm]
  · intro k
    simp_rw [laplaceAmbient_coeff]
    calc
      _ = (laplaceSymbol k : ℂ) * ∑ i : Fin 3, (k i : ℂ) * phaseCoeff q k i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [phaseCoeff_solenoidal q k, mul_zero]

def phaseLaplacian (N : ℕ) : Phase N →ₗ[ℝ] Phase N where
  toFun q := ⟨laplaceAmbient N q, laplaceAmbient_mem N q⟩
  map_add' q r := by
    apply Subtype.ext
    ext ki
    simp [laplaceAmbient, phaseCoeff, extendCoeff, ki.1.property, mul_add]
  map_smul' a q := by
    apply Subtype.ext
    ext ki
    simp [laplaceAmbient, phaseCoeff, extendCoeff, ki.1.property,
      smul_eq_mul, mul_left_comm]

def phaseLaplacianCLM (N : ℕ) : Phase N →L[ℝ] Phase N :=
  { toLinearMap := phaseLaplacian N
    cont := (phaseLaplacian N).continuous_of_finiteDimensional }

theorem phaseLaplacian_coeff (N : ℕ) (q : Phase N) (k : Frequency) (i : Fin 3) :
    phaseCoeff (phaseLaplacian N q) k i = (laplaceSymbol k : ℂ) * phaseCoeff q k i :=
  laplaceAmbient_coeff N q k i

theorem drift_eq_inviscid_sub_laplacian (ν : ℝ) (N : ℕ) (q : Phase N) :
    drift ν N q = drift 0 N q - ν • phaseLaplacian N q := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (drift ν N q) k i =
    phaseCoeff (drift 0 N q - ν • phaseLaplacian N q) k i
  rw [← phaseCoordinate_apply N k i (drift 0 N q - ν • phaseLaplacian N q),
    map_sub, map_smul]
  simp only [phaseCoordinate_apply, phaseLaplacian_coeff]
  rw [drift_coeff_formula, drift_coeff_formula]
  by_cases hk : k ∈ fullModes N
  · rw [if_pos hk, if_pos hk]
    by_cases hzero : k = 0
    · subst k
      simp
    · rw [if_neg hzero, if_neg hzero]
      simp only [zero_mul, Complex.ofReal_zero, neg_zero,
        Complex.ofReal_mul, smul_eq_mul]
      ring
  · rw [if_neg hk, if_neg hk, phaseCoeff_support q k hk i]
    simp

theorem drift_fderiv_viscosity_split (ν : ℝ) (N : ℕ) (q : Phase N) :
    fderiv ℝ (drift ν N) q = fderiv ℝ (drift 0 N) q - ν • phaseLaplacianCLM N := by
  have h0 := ((contDiff_drift 0 N).differentiable (by simp) q).hasFDerivAt
  have hA := (phaseLaplacianCLM N).hasFDerivAt.const_smul ν
  have hd := h0.sub hA
  have heq : (fun z : Phase N => drift 0 N z - ν • phaseLaplacianCLM N z) =
      drift ν N := by
    funext z
    exact (drift_eq_inviscid_sub_laplacian ν N z).symm
  rw [heq] at hd
  exact hd.fderiv


end
end QuantumAdapter.Obligations
