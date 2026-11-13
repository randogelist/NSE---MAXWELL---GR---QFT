import QuantumAdapter.Assembly.Flow
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
Native spatial translations on the full constrained real Fourier phase.
The zero coefficient is retained. These maps are explicit real linear
equivalences; no divergence or flow regularity premise is introduced.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

def translatedAmbient (N : ℕ) (x : Vec) (q : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => fourierCharacter ki.1.val x * phaseCoeff q ki.1.val ki.2)

theorem translatedAmbient_coeff (N : ℕ) (x : Vec) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (translatedAmbient N x q) k i =
      fourierCharacter k x * phaseCoeff q k i := by
  by_cases hk : k ∈ fullModes N
  · simp [extendCoeff, translatedAmbient, hk]
  · simp [extendCoeff, translatedAmbient, hk, phaseCoeff_support q k hk i]

theorem translatedAmbient_mem (N : ℕ) (x : Vec) (q : Phase N) :
    translatedAmbient N x q ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [translatedAmbient_coeff, translatedAmbient_coeff]
    rw [fourierCharacter_neg, phaseCoeff_reality q k i, star_mul]
    exact mul_comm _ _
  · intro k
    simp_rw [translatedAmbient_coeff]
    calc
      (∑ i : Fin 3, (k i : ℂ) *
          (fourierCharacter k x * phaseCoeff q k i)) =
          fourierCharacter k x * ∑ i : Fin 3, (k i : ℂ) * phaseCoeff q k i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [phaseCoeff_solenoidal q k, mul_zero]

def phaseTranslation (N : ℕ) (x : Vec) : Phase N →ₗ[ℝ] Phase N where
  toFun q := ⟨translatedAmbient N x q, translatedAmbient_mem N x q⟩
  map_add' q r := by
    apply Subtype.ext
    ext ki
    simp [translatedAmbient, phaseCoeff, extendCoeff, ki.1.property, mul_add]
  map_smul' a q := by
    apply Subtype.ext
    ext ki
    simp [translatedAmbient, phaseCoeff, extendCoeff, ki.1.property,
      smul_eq_mul, mul_left_comm]

theorem phaseTranslation_coeff (N : ℕ) (x : Vec) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    phaseCoeff (phaseTranslation N x q) k i =
      fourierCharacter k x * phaseCoeff q k i :=
  translatedAmbient_coeff N x q k i

theorem fourierCharacter_zero_space (k : Frequency) :
    fourierCharacter k (0 : Vec) = 1 := by
  simp [fourierCharacter]

theorem fourierCharacter_add_space (k : Frequency) (x y : Vec) :
    fourierCharacter k (x + y) = fourierCharacter k x * fourierCharacter k y := by
  unfold fourierCharacter
  simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierCharacter_neg_space (k : Frequency) (x : Vec) :
    fourierCharacter k (-x) * fourierCharacter k x = 1 := by
  rw [← fourierCharacter_add_space]
  simp [fourierCharacter_zero_space]

theorem phaseTranslation_zero (N : ℕ) (q : Phase N) :
    phaseTranslation N 0 q = q := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (phaseTranslation N 0 q) k i = phaseCoeff q k i
  rw [phaseTranslation_coeff, fourierCharacter_zero_space, one_mul]

theorem phaseTranslation_add (N : ℕ) (x y : Vec) (q : Phase N) :
    phaseTranslation N (x + y) q = phaseTranslation N x (phaseTranslation N y q) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (phaseTranslation N (x + y) q) k i =
    phaseCoeff (phaseTranslation N x (phaseTranslation N y q)) k i
  simp only [phaseTranslation_coeff, fourierCharacter_add_space, mul_assoc]

def phaseTranslationEquiv (N : ℕ) (x : Vec) : Phase N ≃ₗ[ℝ] Phase N where
  __ := phaseTranslation N x
  invFun := phaseTranslation N (-x)
  left_inv q := by
    change phaseTranslation N (-x) (phaseTranslation N x q) = q
    rw [← phaseTranslation_add]
    simp only [neg_add_cancel, phaseTranslation_zero]
  right_inv q := by
    change phaseTranslation N x (phaseTranslation N (-x) q) = q
    rw [← phaseTranslation_add]
    simp only [add_neg_cancel, phaseTranslation_zero]

def phaseTranslationCLE (N : ℕ) (x : Vec) : Phase N ≃L[ℝ] Phase N :=
  (phaseTranslationEquiv N x).toContinuousLinearEquiv

theorem phaseTranslation_mean (N : ℕ) (x : Vec) (q : Phase N) (i : Fin 3) :
    phaseCoeff (phaseTranslation N x q) 0 i = phaseCoeff q 0 i := by
  rw [phaseTranslation_coeff]
  simp [fourierCharacter]

theorem phaseTranslation_meanPhase (N : ℕ) (x : Vec) (m : Vec) :
    phaseTranslation N x (meanPhase N m) = meanPhase N m := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (phaseTranslation N x (meanPhase N m)) k i =
    phaseCoeff (meanPhase N m) k i
  rw [phaseTranslation_coeff, meanPhase_coeff]
  by_cases hk : k = 0
  · subst k
    simp [fourierCharacter]
  · simp [hk]

theorem driftDivergence_eq_linearTrace (ν : ℝ) (N : ℕ) (q : Phase N) :
    driftDivergence ν N q =
      LinearMap.trace ℝ (Phase N) (fderiv ℝ (drift ν N) q).toLinearMap := by
  symm
  exact LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (Phase N))

end
end QuantumAdapter.Obligations
