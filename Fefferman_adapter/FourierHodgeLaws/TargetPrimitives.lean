import MaxwellEndpoint.Constitutive
import SingularClosure.FourierSeriesCalculus

/-!
Exact primitive transport from the retained native Methlib Fourier calculus.
No Fourier convergence or Hodge premise is assumed in these adapters.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical

noncomputable section

theorem native_unitVector (i : Fin 3) :
    SingularClosure.unitVector i = unitVector i := rfl

theorem native_unitCube : SingularClosure.unitCube = unitCube := rfl

theorem native_spatialPeriodic_iff {E : Type*} (f : Vec → E) :
    SingularClosure.SpatialPeriodic f ↔ SpatialPeriodic f := Iff.rfl

theorem native_spatialMean (a : Field) :
    SingularClosure.spatialMean a = spatialMean a := rfl

theorem native_coordinateDerivative (a : Field) (j : Fin 3) :
    SingularClosure.coordinateDerivative a j = coordinateDerivative a j := rfl

theorem native_divergence (a : Field) :
    SingularClosure.divergence a = NSEMaxwell.Classical.divergence a := rfl

theorem native_gradient (f : ScalarField) :
    SingularClosure.gradient f = NSEMaxwell.Classical.gradient f := rfl

theorem native_laplacian (a : Field) :
    SingularClosure.laplacian a = NSEMaxwell.Classical.laplacian a := rfl

/-- Actual scalar Fourier integral on the frozen Euclidean cube. -/
def scalarCoeff (f : ScalarField) (k : Frequency) : ℂ :=
  ∫ x in unitCube,
    star (SingularClosure.fourierCharacter k x) * (f x : ℂ)

/-- A scalar field represented in each coordinate; no solenoidality is used. -/
def scalarLift (f : ScalarField) : Field :=
  fun x => WithLp.toLp 2 (fun _ : Fin 3 => f x)

@[simp]
theorem scalarLift_component (f : ScalarField) (x : Vec) (i : Fin 3) :
    scalarLift f x i = f x := rfl

theorem scalarLift_contDiff (f : ScalarField) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarLift f) := by
  apply (contDiff_piLp 2).2
  intro i
  exact hf

theorem scalarLift_periodic (f : ScalarField) (hf : SpatialPeriodic f) :
    SpatialPeriodic (scalarLift f) := by
  intro x j
  ext i
  exact hf x j

theorem datumFourierCoeff_scalarLift (f : ScalarField) (k : Frequency) (i : Fin 3) :
    SingularClosure.datumFourierCoeff (scalarLift f) k i = scalarCoeff f k := rfl

def inverseVectorCoeff (a : Field) : SingularClosure.FourierCoeff :=
  fun k i => (inverseLaplacianSymbol k : ℂ) * SingularClosure.datumFourierCoeff a k i

def inverseScalarCoeff (f : ScalarField) (k : Frequency) : ℂ :=
  (inverseLaplacianSymbol k : ℂ) * scalarCoeff f k

@[simp]
theorem inverseLaplacianSymbol_zero : inverseLaplacianSymbol 0 = 0 := by
  simp [NSEMaxwell.Classical.inverseLaplacianSymbol]

theorem inverseLaplacianSymbol_neg (k : Frequency) :
    inverseLaplacianSymbol (-k) = inverseLaplacianSymbol k := by
  simp only [NSEMaxwell.Classical.inverseLaplacianSymbol, neg_eq_zero,
    Pi.neg_apply, Int.cast_neg, neg_sq]

theorem inverseLaplacianSymbol_nonneg (k : Frequency) :
    0 ≤ inverseLaplacianSymbol k := by
  unfold NSEMaxwell.Classical.inverseLaplacianSymbol
  split_ifs <;> positivity

theorem inverseLaplacianSymbol_le_one (k : Frequency) :
    inverseLaplacianSymbol k ≤ 1 := by
  classical
  by_cases hk : k = 0
  · subst k
    simp
  have hfZ : (1 : ℤ) ≤ ∑ j : Fin 3, (k j) ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, k i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hk (funext h)
    have hpos : (0 : ℤ) < (k i) ^ 2 := sq_pos_of_ne_zero hi
    have hsum : (k i) ^ 2 ≤ ∑ j : Fin 3, (k j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i)
    omega
  have hf : (1 : ℝ) ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 := by
    exact_mod_cast hfZ
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hden : (1 : ℝ) ≤ 4 * Real.pi ^ 2 * (∑ j : Fin 3, (k j : ℝ) ^ 2) := by
    calc
      1 ≤ 4 * Real.pi ^ 2 := hpi
      _ = 4 * Real.pi ^ 2 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)
  simpa only [NSEMaxwell.Classical.inverseLaplacianSymbol, if_neg hk] using
    inv_le_one_of_one_le₀ hden

theorem inverseLaplacianSymbol_complex_norm_le_one (k : Frequency) :
    ‖(inverseLaplacianSymbol k : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inverseLaplacianSymbol_nonneg k)] using
    inverseLaplacianSymbol_le_one k

@[simp]
theorem inverseVectorCoeff_zero (a : Field) (i : Fin 3) :
    inverseVectorCoeff a 0 i = 0 := by
  simp [inverseVectorCoeff]

@[simp]
theorem inverseScalarCoeff_zero (f : ScalarField) :
    inverseScalarCoeff f 0 = 0 := by
  simp [inverseScalarCoeff]

theorem scalarCoeff_neg (f : ScalarField) (k : Frequency) :
    scalarCoeff f (-k) = star (scalarCoeff f k) := by
  exact SingularClosure.datumFourierCoeff_reality (scalarLift f) k 0

theorem inverseVectorCoeff_reality (a : Field) :
    SingularClosure.SpectralReality (inverseVectorCoeff a) := by
  intro k i
  unfold inverseVectorCoeff
  rw [inverseLaplacianSymbol_neg, SingularClosure.datumFourierCoeff_reality a k i,
    star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]

theorem inverseScalarCoeff_neg (f : ScalarField) (k : Frequency) :
    inverseScalarCoeff f (-k) = star (inverseScalarCoeff f k) := by
  unfold inverseScalarCoeff
  rw [inverseLaplacianSymbol_neg, scalarCoeff_neg, star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]

end

end NSEMaxwell.HodgeProof
