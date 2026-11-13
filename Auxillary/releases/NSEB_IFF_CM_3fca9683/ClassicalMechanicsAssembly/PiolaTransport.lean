import ClassicalMechanics.MaterialBridge

/-!
# Native Piola transport and transformed diffusion

The cofactor identity is composed with actual Frechet product and chain rules.
The final theorem derives the diffusion field of `MaterialPullbackIdentities`
from smooth path geometry and the actual velocity pullback.  A flow existence
theorem is not assumed to have been constructed by this module.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open ClassicalMechanics NSEMaxwell.Classical NSEMaxwell.CurlCurl Set
open scoped BigOperators ContDiff Matrix

noncomputable section

theorem coordinateMinor_smooth {e : Field} (he : ContDiff ℝ ∞ e)
    (j k r s : Fin 3) : ContDiff ℝ ∞ (coordinateMinor e j k r s) := by
  exact ((coordinate_component_smooth he j r).mul
    (coordinate_component_smooth he k s)).sub
      ((coordinate_component_smooth he k r).mul (coordinate_component_smooth he j s))

theorem cofactorGradient_component_smooth {e : Field} (he : ContDiff ℝ ∞ e)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun a => cofactorGradient e a i j) := by
  fin_cases i <;> fin_cases j
  · simpa [cofactorGradient] using coordinateMinor_smooth he 1 2 1 2
  · simpa [cofactorGradient] using coordinateMinor_smooth he 2 0 1 2
  · simpa [cofactorGradient] using coordinateMinor_smooth he 0 1 1 2
  · simpa [cofactorGradient] using coordinateMinor_smooth he 2 1 0 2
  · simpa [cofactorGradient] using coordinateMinor_smooth he 0 2 0 2
  · simpa [cofactorGradient] using coordinateMinor_smooth he 1 0 0 2
  · simpa [cofactorGradient] using coordinateMinor_smooth he 1 2 0 1
  · simpa [cofactorGradient] using coordinateMinor_smooth he 2 0 0 1
  · simpa [cofactorGradient] using coordinateMinor_smooth he 0 1 0 1

theorem vector_fderiv_coordinate_expansion (v : Field) (x w : Vec) (i : Fin 3) :
    fderiv ℝ v x w i = ∑ k : Fin 3, w k * coordinateDerivative v k x i := by
  have h := congrArg (fun z : Vec => fderiv ℝ v x z)
    (NSEMaxwell.Lamb.vector_coordinate_decomposition w)
  have hi := congrArg (fun z : Vec => z i) h
  simpa [Fin.sum_univ_succ, map_add, map_smul, coordinateDerivative,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_assoc] using hi

/-- The matrix chain rule preserves row/component and column/direction order. -/
theorem gradient_matrix_comp {v e : Field}
    (hv : ContDiff ℝ ∞ v) (he : ContDiff ℝ ∞ e) (a : Vec) :
    materialGradientMatrix (fun y => v (e y)) a =
      materialGradientMatrix v (e a) * materialGradientMatrix e a := by
  ext i j
  have hc := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector j) i)
    (((hv.differentiable (by simp) (e a)).hasFDerivAt).comp a
      (he.differentiable (by simp) a).hasFDerivAt).fderiv
  change coordinateDerivative (fun y => v (e y)) j a i =
    fderiv ℝ v (e a) (coordinateDerivative e j a) i at hc
  change coordinateDerivative (fun y => v (e y)) j a i = _
  rw [hc, vector_fderiv_coordinate_expansion]
  simp only [Matrix.mul_apply, materialGradientMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

/-- The polynomial cofactor contraction is valid even for singular gradients. -/
theorem cofactor_contraction (e : Field) (a : Vec) :
    spatialGradientMatrix e a * (cofactorGradient e a).transpose =
      (spatialGradientMatrix e a).det • (1 : StressTensor) := by
  rw [cofactorGradient_eq_adjugate_transpose, Matrix.transpose_transpose,
    Matrix.mul_adjugate]

theorem fderiv_fin3_sum (f : Fin 3 → ScalarField) (a w : Vec)
    (hf : ∀ j : Fin 3, DifferentiableAt ℝ (f j) a) :
    fderiv ℝ (fun y => ∑ j : Fin 3, f j y) a w =
      ∑ j : Fin 3, fderiv ℝ (f j) a w := by
  have hs := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hf j).hasFDerivAt)
  have hh := congrArg (fun L : Vec →L[ℝ] ℝ => L w) hs.fderiv
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.add_apply] using hh

theorem scalar_pullback_product_derivative {e : Field} {q c : ScalarField}
    {a : Vec} (he : DifferentiableAt ℝ e a)
    (hq : DifferentiableAt ℝ q (e a)) (hc : DifferentiableAt ℝ c a)
    (α : Fin 3) :
    fderiv ℝ (fun y => q (e y) * c y) a (unitVector α) =
      (∑ k : Fin 3, fderiv ℝ q (e a) (unitVector k) *
        materialGradientMatrix e a k α) * c a +
      q (e a) * fderiv ℝ c a (unitVector α) := by
  have hcomp : DifferentiableAt ℝ (fun y => q (e y)) a := by
    simpa only [Function.comp_def] using hq.comp a he
  have hchain := gradient_comp_coordinate he hq α
  change fderiv ℝ (fun y => q (e y)) a (unitVector α) =
    ∑ k : Fin 3, materialGradientMatrix e a k α *
      fderiv ℝ q (e a) (unitVector k) at hchain
  erw [fderiv_fun_mul hcomp hc]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hchain]
  simp only [Fin.sum_univ_three]
  ring

theorem tensor_product_pullback_component_derivative {e : Field} {Q : StressField}
    (he : ContDiff ℝ ∞ e)
    (hQ : ∀ i j : Fin 3, Differentiable ℝ (fun x => Q x i j))
    (a : Vec) (i α : Fin 3) :
    fderiv ℝ (fun y => (Q (e y) * cofactorGradient e y) i α) a (unitVector α) =
      ∑ j : Fin 3,
        ((∑ k : Fin 3, fderiv ℝ (fun x => Q x i j) (e a) (unitVector k) *
          materialGradientMatrix e a k α) * cofactorGradient e a j α +
        Q (e a) i j * fderiv ℝ (fun y => cofactorGradient e y j α) a (unitVector α)) := by
  have hcomp (j : Fin 3) : DifferentiableAt ℝ (fun y => Q (e y) i j) a := by
    simpa only [Function.comp_def] using
      (hQ i j (e a)).comp a (he.differentiable (by simp) a)
  have hcof (j : Fin 3) :=
    (cofactorGradient_component_smooth he j α).differentiable (by simp) a
  have hterm (j : Fin 3) :
      DifferentiableAt ℝ (fun y => Q (e y) i j * cofactorGradient e y j α) a := by
    simpa only [Pi.mul_def] using (hcomp j).mul (hcof j)
  have hmatrix : (fun y => (Q (e y) * cofactorGradient e y) i α) =
      (fun y => ∑ j : Fin 3, Q (e y) i j * cofactorGradient e y j α) := by
    funext y
    exact Matrix.mul_apply
  rw [hmatrix, fderiv_fin3_sum _ a (unitVector α) hterm]
  apply Finset.sum_congr rfl
  intro j hj
  exact scalar_pullback_product_derivative
    (he.differentiable (by simp) a) (hQ i j (e a)) (hcof j) α

/-- Finite scalar contraction of the chain term and the divergence-free term. -/
theorem piola_finite_contraction
    (d F C : Fin 3 → Fin 3 → ℝ) (q : Fin 3 → ℝ)
    (dc : Fin 3 → Fin 3 → ℝ) (J : ℝ)
    (hcontract : ∀ k j : Fin 3,
      (∑ α : Fin 3, F k α * C j α) = J * (if k = j then 1 else 0))
    (hdiv : ∀ j : Fin 3, (∑ α : Fin 3, dc j α) = 0) :
    (∑ α : Fin 3, (∑ j : Fin 3,
      ((∑ k : Fin 3, d j k * F k α) * C j α + q j * dc j α))) =
        J * (∑ j : Fin 3, d j j) := by
  calc
    (∑ α : Fin 3, (∑ j : Fin 3,
      ((∑ k : Fin 3, d j k * F k α) * C j α + q j * dc j α))) =
        (∑ j : Fin 3, (∑ k : Fin 3,
          d j k * (∑ α : Fin 3, F k α * C j α))) +
          (∑ j : Fin 3, q j * (∑ α : Fin 3, dc j α)) := by
            simp only [Fin.sum_univ_three]
            ring
    _ = J * (∑ j : Fin 3, d j j) := by
      simp_rw [hcontract, hdiv]
      simp [Fin.sum_univ_three] <;> ring

/-- Full cofactor Piola product transform, without an invertibility premise. -/
theorem piola_product_transform {e : Field} {Q : StressField}
    (he : ContDiff ℝ ∞ e)
    (hQ : ∀ i j : Fin 3, Differentiable ℝ (fun x => Q x i j)) :
    tensorDivergence (fun a => Q (e a) * cofactorGradient e a) =
      fun a => (spatialGradientMatrix e a).det • tensorDivergence Q (e a) := by
  funext a
  apply PiLp.ext
  intro i
  have hcontract (k j : Fin 3) :
      (∑ α : Fin 3, materialGradientMatrix e a k α * cofactorGradient e a j α) =
        (spatialGradientMatrix e a).det * (if k = j then 1 else 0) := by
    have hc := congrArg (fun M : StressTensor => M k j) (cofactor_contraction e a)
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      smul_eq_mul, materialGradientMatrix, spatialGradientMatrix] using hc
  have hdiv (j : Fin 3) :
      (∑ α : Fin 3,
        fderiv ℝ (fun y => cofactorGradient e y j α) a (unitVector α)) = 0 := by
    have hz := congrArg (fun w : Vec => w j) (congrFun (piola_identity he) a)
    exact hz
  change (∑ α : Fin 3,
      fderiv ℝ (fun y => (Q (e y) * cofactorGradient e y) i α) a (unitVector α)) =
    (spatialGradientMatrix e a).det *
      (∑ j : Fin 3, fderiv ℝ (fun x => Q x i j) (e a) (unitVector j))
  simp_rw [tensor_product_pullback_component_derivative he hQ]
  exact piola_finite_contraction
    (fun j k => fderiv ℝ (fun x => Q x i j) (e a) (unitVector k))
    (materialGradientMatrix e a) (cofactorGradient e a) (fun j => Q (e a) i j)
    (fun j α => fderiv ℝ (fun y => cofactorGradient e y j α) a (unitVector α))
    (spatialGradientMatrix e a).det hcontract hdiv

theorem tensorDivergence_gradientMatrix {v : Field} (hv : ContDiff ℝ ∞ v) :
    tensorDivergence (materialGradientMatrix v) = laplacian v := by
  funext x
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3,
    fderiv ℝ (fun y => coordinateDerivative v j y i) x (unitVector j)) =
      laplacian v x i
  simp_rw [second_coordinate_component hv]
  rw [laplacian_coordinate hv x i]
  simp [Fin.sum_univ_succ, add_assoc]

/-- Pullback fixes the material viscosity order as `DV * A * A.transpose`. -/
theorem material_viscous_tensor_pullback {v e V : Field}
    (hv : ContDiff ℝ ∞ v) (he : ContDiff ℝ ∞ e)
    (hV : V = fun a => v (e a))
    (hdet : ∀ a : Vec, (materialGradientMatrix e a).det = 1) (a : Vec) :
    materialGradientMatrix V a * (materialGradientMatrix e a)⁻¹ *
        ((materialGradientMatrix e a)⁻¹).transpose =
      materialGradientMatrix v (e a) * cofactorGradient e a := by
  have hcancel : materialGradientMatrix e a * (materialGradientMatrix e a)⁻¹ = 1 := by
    apply Matrix.mul_nonsing_inv
    rw [hdet a]
    exact isUnit_one
  rw [hV, gradient_matrix_comp hv he,
    Matrix.mul_assoc (materialGradientMatrix v (e a))
      (materialGradientMatrix e a) ((materialGradientMatrix e a)⁻¹),
    hcancel, Matrix.mul_one]
  exact congrArg (fun M : StressTensor => materialGradientMatrix v (e a) * M)
    (cofactorGradient_eq_inverse_transpose_of_det_one e a (hdet a)).symm

/-- The spatial transformed Laplacian follows from smooth pullback and unit Jacobian. -/
theorem spatial_diffusion_pullback {v e V : Field}
    (hv : ContDiff ℝ ∞ v) (he : ContDiff ℝ ∞ e)
    (hV : V = fun a => v (e a))
    (hdet : ∀ a : Vec, (materialGradientMatrix e a).det = 1) :
    tensorDivergence (fun a => materialGradientMatrix V a *
      (materialGradientMatrix e a)⁻¹ * ((materialGradientMatrix e a)⁻¹).transpose) =
        fun a => laplacian v (e a) := by
  have hflux : (fun a => materialGradientMatrix V a *
      (materialGradientMatrix e a)⁻¹ * ((materialGradientMatrix e a)⁻¹).transpose) =
      (fun a => materialGradientMatrix v (e a) * cofactorGradient e a) := by
    funext a
    exact material_viscous_tensor_pullback hv he hV hdet a
  have hQ : ∀ i j : Fin 3,
      Differentiable ℝ (fun x => materialGradientMatrix v x i j) := by
    intro i j
    exact (coordinate_component_smooth hv j i).differentiable (by simp)
  rw [hflux, piola_product_transform he hQ]
  funext a
  have hdet' : (spatialGradientMatrix e a).det = 1 := hdet a
  rw [hdet', one_smul]
  exact congrFun (tensorDivergence_gradientMatrix hv) (e a)

/-- Exact realization of the native diffusion field; no diffusion law remains a premise. -/
theorem CLASSICAL_MECHANICS_DIFFUSION_REALIZATION
    {T : ℝ} {u η ρ : Velocity}
    (hu : SmoothVelocityOn T u) (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a = laplacian (u t) (η t a) := by
  intro t ht a
  have hV : materialVelocity T η t = fun b => u t (η t b) := funext (hflow t ht)
  have hd := spatial_diffusion_pullback
    (finite_velocity_slice_smooth hu ht) (finite_velocity_slice_smooth hη.smooth ht)
    hV (hη.determinant_one t ht)
  exact congrFun hd a

end

end ClassicalMechanicsAssembly
