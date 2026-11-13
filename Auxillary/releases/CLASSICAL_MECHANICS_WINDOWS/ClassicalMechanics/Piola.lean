import ClassicalMechanics.Stress

/-!
# The native three-dimensional Piola cofactor identity

The gradient, minors, and tensor divergence use actual Frechet derivatives.
The cofactor is identified with the transpose of the actual matrix adjugate.
No invertibility, volume-preservation, or Piola-transform premise is required.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical NSEMaxwell.CurlCurl
open scoped BigOperators ContDiff Matrix

noncomputable section

/-- Row = field component; column = differentiation direction. -/
def spatialGradientMatrix (a : Field) : StressField :=
  fun x i j => coordinateDerivative a j x i

/-- A two-by-two minor with ordered derivative columns and field rows. -/
def coordinateMinor (a : Field) (j k r s : Fin 3) : ScalarField :=
  fun x => coordinateDerivative a j x r * coordinateDerivative a k x s -
    coordinateDerivative a k x r * coordinateDerivative a j x s

theorem coordinateMinor_derivative
    {a : Field} (ha : ContDiff ℝ ∞ a) (i j k r s : Fin 3) (x : Vec) :
    fderiv ℝ (coordinateMinor a j k r s) x (unitVector i) =
      secondCoordinate a i j x r * coordinateDerivative a k x s +
        coordinateDerivative a j x r * secondCoordinate a i k x s -
        (secondCoordinate a i k x r * coordinateDerivative a j x s +
          coordinateDerivative a k x r * secondCoordinate a i j x s) := by
  have hjr := (coordinate_component_smooth ha j r).differentiable (by simp) x
  have hks := (coordinate_component_smooth ha k s).differentiable (by simp) x
  have hkr := (coordinate_component_smooth ha k r).differentiable (by simp) x
  have hjs := (coordinate_component_smooth ha j s).differentiable (by simp) x
  have hleft : DifferentiableAt ℝ (fun y : Vec =>
      coordinateDerivative a j y r * coordinateDerivative a k y s) x := by
    simpa only [Pi.mul_def] using hjr.mul hks
  have hright : DifferentiableAt ℝ (fun y : Vec =>
      coordinateDerivative a k y r * coordinateDerivative a j y s) x := by
    simpa only [Pi.mul_def] using hkr.mul hjs
  unfold coordinateMinor
  erw [fderiv_fun_sub hleft hright, fderiv_fun_mul hjr hks,
    fderiv_fun_mul hkr hjs]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, second_coordinate_component ha]
  ring

/-- Native cofactor matrix, written as its nine signed minors. -/
def cofactorGradient (a : Field) : StressField := fun x =>
  !![coordinateMinor a 1 2 1 2 x, coordinateMinor a 2 0 1 2 x,
      coordinateMinor a 0 1 1 2 x;
    coordinateMinor a 2 1 0 2 x, coordinateMinor a 0 2 0 2 x,
      coordinateMinor a 1 0 0 2 x;
    coordinateMinor a 1 2 0 1 x, coordinateMinor a 2 0 0 1 x,
      coordinateMinor a 0 1 0 1 x]

/-- The explicit minors are exactly the transpose of the actual adjugate. -/
theorem cofactorGradient_eq_adjugate_transpose (a : Field) (x : Vec) :
    cofactorGradient a x = (spatialGradientMatrix a x).adjugate.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactorGradient, coordinateMinor, spatialGradientMatrix,
      Matrix.transpose_apply, Matrix.adjugate_fin_three] <;> ring

/-- Piola: every row of the cofactor of a smooth gradient is divergence-free. -/
theorem piola_identity {a : Field} (ha : ContDiff ℝ ∞ a) :
    tensorDivergence (cofactorGradient a) = 0 := by
  funext x
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3,
    fderiv ℝ (fun y : Vec => cofactorGradient a y i j) x (unitVector j)) = 0
  rw [Fin.sum_univ_three]
  fin_cases i <;>
    simp [cofactorGradient, coordinateMinor_derivative ha,
      secondCoordinate_symm ha 1 0 x, secondCoordinate_symm ha 2 0 x,
      secondCoordinate_symm ha 2 1 x] <;> ring

/-- Piola identity stated directly for Mathlib's matrix adjugate. -/
theorem tensorDivergence_adjugate_gradient
    {a : Field} (ha : ContDiff ℝ ∞ a) :
    tensorDivergence (fun x => (spatialGradientMatrix a x).adjugate.transpose) = 0 := by
  have hcofactor : (fun x => (spatialGradientMatrix a x).adjugate.transpose) =
      cofactorGradient a := by
    funext x
    exact (cofactorGradient_eq_adjugate_transpose a x).symm
  rw [hcofactor]
  exact piola_identity ha

/-- At unit Jacobian the cofactor is exactly the inverse transpose. -/
theorem cofactorGradient_eq_inverse_transpose_of_det_one
    (a : Field) (x : Vec) (hdet : (spatialGradientMatrix a x).det = 1) :
    cofactorGradient a x = ((spatialGradientMatrix a x)⁻¹).transpose := by
  rw [cofactorGradient_eq_adjugate_transpose, Matrix.inv_def, hdet]
  simp

/-- Incompressible Piola: divergence of the actual inverse transpose vanishes. -/
theorem tensorDivergence_inverse_transpose_of_det_one
    {a : Field} (ha : ContDiff ℝ ∞ a)
    (hdet : ∀ x : Vec, (spatialGradientMatrix a x).det = 1) :
    tensorDivergence (fun x => ((spatialGradientMatrix a x)⁻¹).transpose) = 0 := by
  have hcofactor : (fun x => ((spatialGradientMatrix a x)⁻¹).transpose) =
      cofactorGradient a := by
    funext x
    exact (cofactorGradient_eq_inverse_transpose_of_det_one a x (hdet x)).symm
  rw [hcofactor]
  exact piola_identity ha

end

end ClassicalMechanics
