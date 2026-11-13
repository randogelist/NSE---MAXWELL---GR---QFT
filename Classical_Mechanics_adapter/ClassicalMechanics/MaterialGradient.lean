import ClassicalMechanics.Material
import NSEMaxwell.Lamb

/-!
# Native material pressure-gradient pullback

The scalar Frechet chain rule supplies `grad (p ∘ eta) = Fᵀ grad p`.
The actual matrix inverse cancels `Fᵀ` when `det F` is nonzero.  Thus the
pressure-gradient field of `MaterialPullbackIdentities` requires no separate
analytic assumption once the smooth geometric path and literal pressure
pullback have been supplied.
-/

set_option autoImplicit false

open Set
open scoped BigOperators ContDiff

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

theorem scalar_fderiv_coordinate_expansion (p : ScalarField) (x v : Vec) :
    fderiv ℝ p x v =
      ∑ j : Fin 3, v j * NSEMaxwell.Classical.gradient p x j := by
  have h := congrArg (fun w : Vec => fderiv ℝ p x w)
    (NSEMaxwell.Lamb.vector_coordinate_decomposition v)
  simpa [Fin.sum_univ_succ, map_add, map_smul,
    NSEMaxwell.Classical.gradient, PiLp.toLp_apply, smul_eq_mul, add_assoc] using h

theorem gradient_comp_coordinate {η : Field} {p : ScalarField} {a : Vec}
    (hη : DifferentiableAt ℝ η a) (hp : DifferentiableAt ℝ p (η a))
    (i : Fin 3) :
    NSEMaxwell.Classical.gradient (fun y => p (η y)) a i =
      ∑ j : Fin 3, materialGradientMatrix η a j i *
        NSEMaxwell.Classical.gradient p (η a) j := by
  change fderiv ℝ (fun y => p (η y)) a (unitVector i) = _
  have hc := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i))
    (hp.hasFDerivAt.comp a hη.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => p (η y)) a (unitVector i) =
    fderiv ℝ p (η a) (fderiv ℝ η a (unitVector i)) at hc
  exact hc.trans
    (scalar_fderiv_coordinate_expansion p (η a) (fderiv ℝ η a (unitVector i)))

theorem inverse_transpose_gradient_chain {F : StressTensor}
    (hF : F.det ≠ 0) (g : Fin 3 → ℝ) :
    (F⁻¹).transpose.mulVec (F.transpose.mulVec g) = g := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv F (isUnit_iff_ne_zero.mpr hF), Matrix.transpose_one,
    Matrix.one_mulVec]

/-- Pointwise gradient pullback from actual differentiability and matrix invertibility. -/
theorem material_pressure_gradient_of_pullback
    {η : Velocity} {p π : Pressure} {t : ℝ} {a : Vec}
    (hη : DifferentiableAt ℝ (η t) a)
    (hp : DifferentiableAt ℝ (p t) (η t a))
    (hF : (deformationGradient η t a).det ≠ 0)
    (hπ : π t = fun y => p t (η t y)) :
    materialPressureGradient η π t a =
      NSEMaxwell.Classical.gradient (p t) (η t a) := by
  let F : StressTensor := deformationGradient η t a
  let g : Fin 3 → ℝ := fun i => NSEMaxwell.Classical.gradient (p t) (η t a) i
  have hchain :
      (fun i : Fin 3 => NSEMaxwell.Classical.gradient (π t) a i) =
        F.transpose.mulVec g := by
    funext i
    rw [hπ]
    exact gradient_comp_coordinate hη hp i
  apply PiLp.ext
  intro i
  change ((F⁻¹).transpose.mulVec
    (fun j : Fin 3 => NSEMaxwell.Classical.gradient (π t) a j)) i = g i
  rw [hchain, inverse_transpose_gradient_chain hF g]

/-- Finite-slab specialization discharges the gradient identity from path geometry. -/
theorem material_pressure_gradient_pullback_on
    {T : ℝ} {η ρ : Velocity} {p π : Pressure}
    (hη : MaterialPathOn T η ρ) (hp : SmoothPressureOn T p)
    (hπ : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, π t a = p t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialPressureGradient η π t a =
        NSEMaxwell.Classical.gradient (p t) (η t a) := by
  intro t ht a
  exact material_pressure_gradient_of_pullback
    ((finite_velocity_slice_smooth hη.smooth ht).differentiable (by simp) a)
    ((finite_pressure_slice_smooth hp ht).differentiable (by simp) (η t a))
    (deformation_det_ne_zero hη ht a) (funext (hπ t ht))

end

end ClassicalMechanics
