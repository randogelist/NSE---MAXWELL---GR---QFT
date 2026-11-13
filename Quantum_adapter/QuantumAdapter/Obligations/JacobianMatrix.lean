import Mathlib

/-!
# Determinant along a finite-dimensional variational equation

The matrix argument works at singular matrices.  It uses the polynomial
expansion at the identity and differentiability of the determinant, rather
than an inverse-matrix formula.
-/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

namespace QuantumAdapter.Obligations

noncomputable section

open scoped BigOperators Polynomial Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_differentiable :
    Differentiable ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change Differentiable ℝ (fun M : Matrix ι ι ℝ => M.det)
  simp_rw [Matrix.det_apply']
  fun_prop

theorem matrix_det_one_add_smul_hasDerivAt (A : Matrix ι ι ℝ) :
    HasDerivAt (fun s : ℝ => (1 + s • A).det) A.trace 0 := by
  let Q : ℝ[X] :=
    (Matrix.det (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C)).divX.divX
  have hlin : HasDerivAt (fun s : ℝ => 1 + A.trace * s) A.trace 0 := by
    simpa only [mul_one] using!
      (((hasDerivAt_id (0 : ℝ)).const_mul A.trace).const_add (1 : ℝ))
  have hquad : HasDerivAt (fun s : ℝ => Q.eval s * s ^ 2) 0 0 := by
    simpa [Pi.mul_apply, Pi.pow_apply] using!
      (Q.hasDerivAt (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).pow 2)
  convert! hlin.fun_add hquad using 1
  · ext s
    exact Matrix.det_one_add_smul s A
  · simp

theorem matrix_det_affine_left_hasDerivAt (A J : Matrix ι ι ℝ) :
    HasDerivAt (fun s : ℝ => (J + s • (A * J)).det)
      (A.trace * J.det) 0 := by
  have h := (matrix_det_one_add_smul_hasDerivAt A).mul_const J.det
  convert! h using 1
  ext s
  rw [← Matrix.det_mul]
  congr 1
  simp [add_mul, smul_mul_assoc]

theorem matrix_det_fderiv_left_mul (A J : Matrix ι ι ℝ) :
    fderiv ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) J (A * J) =
      A.trace * J.det := by
  have hline : HasDerivAt (fun s : ℝ => J + s • (A * J)) (A * J) 0 := by
    simpa only [one_smul] using!
      (((hasDerivAt_id (0 : ℝ)).smul_const (A * J)).const_add J)
  have hdet : HasFDerivAt (Matrix.det : Matrix ι ι ℝ → ℝ)
      (fderiv ℝ Matrix.det J) (J + (0 : ℝ) • (A * J)) := by
    simpa only [zero_smul, add_zero] using! (matrix_det_differentiable J).hasFDerivAt
  have h := hdet.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero, Function.comp_apply] using!
    h.unique (matrix_det_affine_left_hasDerivAt A J)

theorem matrix_det_hasDerivAt_of_left_mul
    {J : ℝ → Matrix ι ι ℝ} {A : Matrix ι ι ℝ} {t : ℝ}
    (hJ : HasDerivAt J (A * J t) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t := by
  have h := (matrix_det_differentiable (J t)).hasFDerivAt.comp_hasDerivAt t hJ
  simpa only [Function.comp_apply, matrix_det_fderiv_left_mul] using! h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Matrix coordinates as a continuous linear map on endomorphisms. -/
def endomorphismMatrixCLM (b : Module.Basis ι ℝ E) :
    (E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ :=
  ((LinearMap.toMatrix b b).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

@[simp]
theorem endomorphismMatrixCLM_apply (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    endomorphismMatrixCLM b A = LinearMap.toMatrix b b A.toLinearMap := rfl

theorem endomorphismMatrixCLM_comp (b : Module.Basis ι ℝ E) (A J : E →L[ℝ] E) :
    endomorphismMatrixCLM b (A.comp J) =
      endomorphismMatrixCLM b A * endomorphismMatrixCLM b J := by
  change LinearMap.toMatrix b b (A.toLinearMap.comp J.toLinearMap) = _
  exact LinearMap.toMatrix_comp b b b A.toLinearMap J.toLinearMap

theorem endomorphismMatrixCLM_det (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    (endomorphismMatrixCLM b A).det = A.det := by
  exact LinearMap.det_toMatrix b A.toLinearMap

theorem endomorphismMatrixCLM_trace (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    (endomorphismMatrixCLM b A).trace = LinearMap.trace ℝ E A.toLinearMap := by
  exact (LinearMap.trace_eq_matrix_trace ℝ b A.toLinearMap).symm

/-- Jacobi--Liouville identity without a nonsingularity hypothesis. -/
theorem clm_det_hasDerivAt_of_comp
    {J : ℝ → E →L[ℝ] E} {A : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J (A.comp (J t)) t) :
    HasDerivAt (fun s => (J s).det)
      (LinearMap.trace ℝ E A.toLinearMap * (J t).det) t := by
  classical
  let b := Module.finBasis ℝ E
  have hm := (endomorphismMatrixCLM b).hasFDerivAt.comp_hasDerivAt t hJ
  have hm' : HasDerivAt (fun s => endomorphismMatrixCLM b (J s))
      (endomorphismMatrixCLM b A * endomorphismMatrixCLM b (J t)) t := by
    simpa only [Function.comp_apply, endomorphismMatrixCLM_comp] using! hm
  simpa only [endomorphismMatrixCLM_trace, endomorphismMatrixCLM_det] using!
    matrix_det_hasDerivAt_of_left_mul hm'

/-- Exact signed-time exponential determinant from a constant real trace. -/
theorem clm_det_eq_exp_of_constant_trace
    (J A : ℝ → E →L[ℝ] E) (c : ℝ)
    (hJ : ∀ t, HasDerivAt J ((A t).comp (J t)) t)
    (hzero : J 0 = ContinuousLinearMap.id ℝ E)
    (htrace : ∀ t, LinearMap.trace ℝ E (A t).toLinearMap = c)
    (t : ℝ) : (J t).det = Real.exp (c * t) := by
  have hd (s : ℝ) : HasDerivAt (fun r => (J r).det) (c * (J s).det) s := by
    simpa only [htrace s] using! clm_det_hasDerivAt_of_comp (hJ s)
  have hf (s : ℝ) :
      HasDerivAt (fun r => Real.exp (-c * r) * (J r).det) 0 s := by
    have he := ((hasDerivAt_id s).const_mul (-c)).exp
    convert! he.fun_mul (hd s) using 1 <;> ring
  have hc := is_const_of_deriv_eq_zero
    (fun s => (hf s).differentiableAt) (fun s => (hf s).deriv) t 0
  have hvalue : Real.exp (-c * t) * (J t).det = 1 := by
    simpa [hzero, ContinuousLinearMap.det] using hc
  have hexp : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    (J t).det = (Real.exp (c * t) * Real.exp (-c * t)) * (J t).det := by
      rw [hexp, one_mul]
    _ = Real.exp (c * t) * (Real.exp (-c * t) * (J t).det) := mul_assoc _ _ _
    _ = Real.exp (c * t) := by rw [hvalue, mul_one]

end
end QuantumAdapter.Obligations
