import NSEMaxwell.CurlCurl

/-!
Actual Newtonian stress and its row divergence on the periodic Euclidean
representation. No Fourier or Hodge law is used. All derivative identities
are consequences of the supplied smooth fields and native coordinate calculus.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical NSEMaxwell.CurlCurl
open scoped BigOperators ContDiff

noncomputable section

abbrev StressTensor := Matrix (Fin 3) (Fin 3) ℝ
abbrev StressField := Vec → StressTensor

/-- Symmetric velocity gradient, with row = velocity component. -/
def strain (a : Field) : StressField := fun x i j =>
  (coordinateDerivative a j x i + coordinateDerivative a i x j) / 2

/-- Unit-density Newtonian constitutive stress. -/
def newtonianStress (ν : ℝ) (a : Field) (p : ScalarField) : StressField :=
  fun x i j =>
    (if i = j then -p x else 0) +
      ν * (coordinateDerivative a j x i + coordinateDerivative a i x j)

/-- Actual row divergence: `(div σ)_i = sum_j partial_j σ_ij`. -/
def tensorDivergence (σ : StressField) : Field := fun x =>
  WithLp.toLp 2 (fun i : Fin 3 =>
    ∑ j : Fin 3, fderiv ℝ (fun y : Vec => σ y i j) x (unitVector j))

theorem strain_symmetric (a : Field) (x : Vec) (i j : Fin 3) :
    strain a x i j = strain a x j i := by
  simp [strain, add_comm]

theorem newtonianStress_constitutive
    (ν : ℝ) (a : Field) (p : ScalarField) (x : Vec) (i j : Fin 3) :
    newtonianStress ν a p x i j =
      -p x * (if i = j then 1 else 0) + 2 * ν * strain a x i j := by
  by_cases hij : i = j <;> simp [newtonianStress, strain, hij] <;> ring

theorem newtonianStress_symmetric
    (ν : ℝ) (a : Field) (p : ScalarField) (x : Vec) (i j : Fin 3) :
    newtonianStress ν a p x i j = newtonianStress ν a p x j i := by
  simp [newtonianStress, eq_comm, add_comm]

/-- Every stress entry has its actual scalar Frechet derivative. -/
theorem newtonianStress_component_derivative
    (ν : ℝ) {a : Field} {p : ScalarField}
    (ha : ContDiff ℝ ∞ a) (hp : ContDiff ℝ ∞ p)
    (i j k : Fin 3) (x : Vec) :
    fderiv ℝ (fun y : Vec => newtonianStress ν a p y i j) x (unitVector k) =
      (if i = j then -NSEMaxwell.Classical.gradient p x k else 0) +
        ν * (secondCoordinate a k j x i + secondCoordinate a k i x j) := by
  have hp' := (hp.differentiable (by simp) x).hasFDerivAt
  have hji := ((coordinate_component_smooth ha j i).differentiable (by simp) x).hasFDerivAt
  have hij' := ((coordinate_component_smooth ha i j).differentiable (by simp) x).hasFDerivAt
  have hpressure : HasFDerivAt (fun y : Vec => if i = j then -p y else 0)
      (if i = j then -(fderiv ℝ p x) else 0) x := by
    by_cases hij : i = j
    · simpa only [hij, if_true] using hp'.neg
    · simpa only [hij, if_false] using (hasFDerivAt_const (0 : ℝ) x)
  have h := hpressure.add ((hji.add hij').const_mul ν)
  have he := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector k)) h.fderiv
  by_cases hij : i = j
  · simpa [newtonianStress, hij, NSEMaxwell.Classical.gradient, PiLp.toLp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, smul_eq_mul, second_coordinate_component ha] using he
  · simpa [newtonianStress, hij, NSEMaxwell.Classical.gradient, PiLp.toLp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, second_coordinate_component ha] using he

/-- The full identity retains the compressible `grad div` contribution. -/
theorem tensorDivergence_newtonianStress
    (ν : ℝ) {a : Field} {p : ScalarField}
    (ha : ContDiff ℝ ∞ a) (hp : ContDiff ℝ ∞ p) :
    tensorDivergence (newtonianStress ν a p) =
      -NSEMaxwell.Classical.gradient p + ν • NSEMaxwell.Classical.laplacian a +
        ν • NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) := by
  funext x
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3,
      fderiv ℝ (fun y : Vec => newtonianStress ν a p y i j) x (unitVector j)) =
    -NSEMaxwell.Classical.gradient p x i +
      ν * NSEMaxwell.Classical.laplacian a x i +
        ν * NSEMaxwell.Classical.gradient (NSEMaxwell.Classical.divergence a) x i
  simp_rw [newtonianStress_component_derivative ν ha hp]
  rw [laplacian_coordinate ha x i, gradient_divergence_coordinate ha i x]
  fin_cases i <;>
    simp [Fin.sum_univ_succ, secondCoordinate_symm ha 1 0 x,
      secondCoordinate_symm ha 2 0 x, secondCoordinate_symm ha 2 1 x] <;> ring

/-- Incompressibility removes the actual gradient of the divergence. -/
theorem tensorDivergence_newtonianStress_of_divergence_zero
    (ν : ℝ) {a : Field} {p : ScalarField}
    (ha : ContDiff ℝ ∞ a) (hp : ContDiff ℝ ∞ p)
    (hDiv : NSEMaxwell.Classical.divergence a = 0) :
    tensorDivergence (newtonianStress ν a p) =
      -NSEMaxwell.Classical.gradient p + ν • NSEMaxwell.Classical.laplacian a := by
  rw [tensorDivergence_newtonianStress ν ha hp, hDiv, gradient_zero, smul_zero, add_zero]

end

end ClassicalMechanics
