import NSEMaxwell.Classical

/-!
# Concrete Lamb identity

The proof uses the actual Euclidean-space derivative, coordinate curl, cross
product, convection, and NSEMaxwell.Classical.gradient from Classical.lean. The only hypothesis of
the pointwise identity is ordinary differentiability of the vector field at the
point. No Fourier, Hodge, incompressibility, or Lamb-identity premise is used.

Proof spine: three-coordinate vector expansion; linearity of the Frechet
derivative; norm-square chain rule; coordinate polynomial identities.

Compilation evidence is supplied by the external native Windows runner.
No local Lean or Lake execution is performed.
-/

set_option autoImplicit false

namespace NSEMaxwell.Lamb

open NSEMaxwell.Classical
open scoped ContDiff

noncomputable section

/-- The explicit three-dimensional coordinate decomposition. -/
theorem vector_coordinate_decomposition (v : Vec) :
    v = v 0 • unitVector 0 + v 1 • unitVector 1 + v 2 • unitVector 2 := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [unitVector, EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]

/-- Linearity of the actual Frechet derivative expands the convection term. -/
theorem convection_coordinate (a : Field) (x : Vec) (i : Fin 3) :
    convection a x i =
      a x 0 * coordinateDerivative a 0 x i +
      a x 1 * coordinateDerivative a 1 x i +
      a x 2 * coordinateDerivative a 2 x i := by
  have h := congrArg (fun v : Vec => fderiv ℝ a x v)
    (vector_coordinate_decomposition (a x))
  have hi := congrArg (fun v : Vec => v i) h
  simpa only [convection, coordinateDerivative, map_add, map_smul,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hi

/-- The kinetic-energy NSEMaxwell.Classical.gradient, proved by the norm-square chain rule. -/
theorem kinetic_gradient_coordinate
    {a : Field} {x : Vec} (ha : DifferentiableAt ℝ a x) (i : Fin 3) :
    NSEMaxwell.Classical.gradient (fun y : Vec => ‖a y‖ ^ 2 / 2) x i =
      a x 0 * coordinateDerivative a i x 0 +
      a x 1 * coordinateDerivative a i x 1 +
      a x 2 * coordinateDerivative a i x 2 := by
  change fderiv ℝ (fun y : Vec => ‖a y‖ ^ 2 / 2) x (unitVector i) = _
  have hnorm := ha.hasFDerivAt.norm_sq.const_mul (1 / 2 : ℝ)
  have hfun :
      (fun y : Vec => ‖a y‖ ^ 2 / 2) =
        (fun y : Vec => (1 / 2 : ℝ) * ‖a y‖ ^ 2) := by
    funext y
    ring
  calc
    fderiv ℝ (fun y : Vec => ‖a y‖ ^ 2 / 2) x (unitVector i) =
        inner ℝ (a x) (coordinateDerivative a i x) := by
      rw [hfun, hnorm.fderiv]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, innerSL_apply_apply, two_smul,
        smul_eq_mul, coordinateDerivative]
      ring
    _ = a x 0 * coordinateDerivative a i x 0 +
        a x 1 * coordinateDerivative a i x 1 +
        a x 2 * coordinateDerivative a i x 2 := by
      simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

/--
The concrete pointwise identity:
(a dot grad) a = (curl a) cross a + grad (norm a squared / 2).
-/
theorem lamb_identity_at
    {a : Field} {x : Vec} (ha : DifferentiableAt ℝ a x) :
    convection a x =
      cross (spatialCurl a x) (a x) +
        NSEMaxwell.Classical.gradient (fun y : Vec => ‖a y‖ ^ 2 / 2) x := by
  apply PiLp.ext
  intro i
  rw [PiLp.add_apply, convection_coordinate a x i, kinetic_gradient_coordinate ha i]
  fin_cases i <;> simp [cross, spatialCurl, PiLp.toLp_apply] <;> ring

/-- Field-valued Lamb identity for every differentiable vector field. -/
theorem lamb_identity
    {a : Field} (ha : Differentiable ℝ a) :
    convection a =
      (fun x : Vec => cross (spatialCurl a x) (a x)) +
        NSEMaxwell.Classical.gradient (fun x : Vec => ‖a x‖ ^ 2 / 2) := by
  funext x
  exact lamb_identity_at (ha x)

/-- Smooth data satisfy the identity; divergence and periodicity are unused. -/
theorem lamb_identity_of_data
    {a : Field} (ha : Data a) :
    convection a =
      (fun x : Vec => cross (spatialCurl a x) (a x)) +
        NSEMaxwell.Classical.gradient (fun x : Vec => ‖a x‖ ^ 2 / 2) := by
  exact lamb_identity (ha.smooth.differentiable (by simp))

/--
For the canonical velocity, the independent curl-reconstruction equality
identifies the vorticity in the proved Lamb identity with B.
-/
theorem reconstructed_lamb_identity
    (m : Vec) (B : Field)
    (hData : Data (U m B))
    (hCurl : spatialCurl (U m B) = B) :
    convection (U m B) =
      (fun x : Vec => cross (B x) (U m B x)) +
        NSEMaxwell.Classical.gradient (fun x : Vec => ‖U m B x‖ ^ 2 / 2) := by
  simpa only [hCurl] using lamb_identity_of_data hData

end

end NSEMaxwell.Lamb

