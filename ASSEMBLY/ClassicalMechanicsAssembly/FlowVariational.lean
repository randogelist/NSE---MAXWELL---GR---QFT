import ClassicalMechanicsAssembly.FlowJacobian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Actual variational equation on a closed finite slab

Joint smoothness and the actual flow ODE imply the deformation-gradient ODE.
The equality of the mixed derivatives holds at both interval endpoints by
symmetry of the second derivative within the closed slab.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open ClassicalMechanics NSEMaxwell.Classical Set
open scoped ContDiff

noncomputable section

theorem closure_interior_finiteSpacetime {T : ℝ} (hT : 0 < T) :
    closure (interior (finiteSpacetime T)) = finiteSpacetime T := by
  have heq : finiteSpacetime T = Icc (0 : ℝ) T ×ˢ (univ : Set Vec) := by
    ext z
    simp [finiteSpacetime]
  rw [heq, interior_prod_eq, interior_Icc, interior_univ, closure_prod_eq,
    closure_Ioo (ne_of_lt hT), closure_univ]

/-- The second actual within derivative is symmetric, including the slab boundary. -/
theorem finite_spacetime_second_derivative_symmetric
    {T : ℝ} (hT : 0 < T) {η : Velocity} (hη : SmoothVelocityOn T η)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    IsSymmSndFDerivWithinAt ℝ (fun z : ℝ × Vec => η z.1 z.2)
      (finiteSpacetime T) (t, a) := by
  apply (hη (t, a) ht).isSymmSndFDerivWithinAt
    (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      decide)
    (uniqueDiffOn_finiteSpacetime hT) _ ht
  rw [closure_interior_finiteSpacetime hT]
  exact ht

/-- The actual time derivative of a spatial directional derivative. -/
theorem finite_mixed_directional_hasDerivWithinAt
    {T : ℝ} (hT : 0 < T) {η : Velocity} (hη : SmoothVelocityOn T η)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a v : Vec) :
    HasDerivWithinAt (fun s => fderiv ℝ (η s) a v)
      (fderiv ℝ (finiteTimeDerivative T η t) a v) (Icc (0 : ℝ) T) t := by
  let L := fderivWithin ℝ (fun z : ℝ × Vec => η z.1 z.2) (finiteSpacetime T)
  let H := fderivWithin ℝ L (finiteSpacetime T) (t, a)
  have hL : ContDiffWithinAt ℝ 1 L (finiteSpacetime T) (t, a) :=
    (hη (t, a) ht).fderivWithin_right (uniqueDiffOn_finiteSpacetime hT)
      (by simp) ht
  have hdL : HasFDerivWithinAt L H (finiteSpacetime T) (t, a) :=
    (hL.differentiableWithinAt (by simp)).hasFDerivWithinAt
  have heTime : HasDerivWithinAt (fun s : ℝ => (s, a)) (1, 0)
      (Icc (0 : ℝ) T) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t a)).hasDerivWithinAt
  have hTime : HasDerivWithinAt (fun s => L (s, a)) (H (1, 0))
      (Icc (0 : ℝ) T) t := by
    simpa only [Function.comp_def] using
      hdL.comp_hasDerivWithinAt t heTime (fun _ hs => hs)
  have hTimeApply : HasDerivWithinAt (fun s => L (s, a) (0, v))
      (H (1, 0) (0, v)) (Icc (0 : ℝ) T) t := by
    simpa only [map_zero, add_zero] using
      hTime.clm_apply (hasDerivAt_const t ((0 : ℝ), v)).hasDerivWithinAt
  have heSpace := (hasFDerivAt_const (𝕜 := ℝ) t a).prodMk (hasFDerivAt_id a)
  have hSpace := hdL.comp_hasFDerivAt a heSpace
    (Filter.Eventually.of_forall (fun _ => ht))
  have hSpaceApply := hSpace.clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) ((1 : ℝ), (0 : Vec)) a)
  have hSpaceValue : fderiv ℝ (fun b => L (t, b) (1, 0)) a v =
      H (0, v) (1, 0) := by
    have hv := congrArg (fun K : Vec →L[ℝ] Vec => K v) hSpaceApply.fderiv
    simpa [Function.comp_def] using hv
  have hTimeField : finiteTimeDerivative T η t = fun b => L (t, b) (1, 0) := by
    funext b
    exact finite_time_restriction_fderiv hT hη ht b
  have hMixed : H (1, 0) (0, v) =
      fderiv ℝ (finiteTimeDerivative T η t) a v := by
    rw [hTimeField, hSpaceValue]
    exact (finite_spacetime_second_derivative_symmetric hT hη ht a).eq
      (1, 0) (0, v)
  rw [hMixed] at hTimeApply
  apply hTimeApply.congr_of_mem _ ht
  intro s hs
  exact finite_spatial_restriction_fderiv hη hs a v

/-- Time differentiation of the actual deformation gradient commutes with spatial differentiation. -/
theorem deformationGradient_hasDerivWithinAt
    {T : ℝ} (hT : 0 < T) {η : Velocity} (hη : SmoothVelocityOn T η)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    HasDerivWithinAt (fun s => deformationGradient η s a)
      (materialGradientMatrix (finiteTimeDerivative T η t) a)
      (Icc (0 : ℝ) T) t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  have hcol := finite_mixed_directional_hasDerivWithinAt hT hη ht a (unitVector j)
  have hc := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
    (fderiv ℝ (η t) a (unitVector j)) i).comp_hasDerivWithinAt t hcol
  exact hc

/-- E13: the native variational ODE follows from smoothness and the actual flow ODE. -/
theorem FLOW_VARIATIONAL_ODE
    {T : ℝ} (hT : 0 < T) {u η : Velocity}
    (hu : SmoothVelocityOn T u) (hη : SmoothVelocityOn T η)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      finiteTimeDerivative T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      HasDerivWithinAt (fun s => deformationGradient η s a)
        (materialGradientMatrix (u t) (η t a) * deformationGradient η t a)
        (Icc (0 : ℝ) T) t := by
  intro t ht a
  have hv : finiteTimeDerivative T η t = fun b => u t (η t b) := funext (hflow t ht)
  have hc := deformationGradient_hasDerivWithinAt hT hη ht a
  rw [hv, gradient_matrix_comp (finite_velocity_slice_smooth hu ht)
    (finite_velocity_slice_smooth hη ht)] at hc
  exact hc

/-- E14: a smooth incompressible flow with identity initial configuration has unit Jacobian. -/
theorem FLOW_JACOBIAN_ONE
    {T : ℝ} (hT : 0 < T) {u η : Velocity}
    (hu : SmoothVelocityOn T u) (hη : SmoothVelocityOn T η)
    (hη0 : η 0 = fun a : Vec => a)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      finiteTimeDerivative T η t a = u t (η t a))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, (deformationGradient η t a).det = 1 :=
  FLOW_JACOBIAN_ONE_OF_VARIATIONAL_ODE hT hη0 (FLOW_VARIATIONAL_ODE hT hu hη hflow) hdiv

end

end ClassicalMechanicsAssembly
