import GRAssembly.BoundaryConstraintsGeometry
import GRAssembly.NativeGluingGaussianCoordinates

/-!
Coordinate differential identities for the native Gaussian-jet construction.
All derivatives are actual Frechet derivatives. This file starts with the
endomorphism-valued differential Bianchi identity; its geometric contraction
will use the literal native Christoffel symbols and metric compatibility.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 3200000

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

noncomputable section

section CoordinateDerivatives

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Directional coordinate derivative with an arbitrary normed target. -/
def coordDeriv (f : Bulk → F) (i : Fin 5) (z : Bulk) : F :=
  fderiv ℝ f z (bulkBasis i)

theorem coordDeriv_scalar (f : Bulk → ℝ) (i : Fin 5) (z : Bulk) :
    coordDeriv f i z = bulkPartial f i z := rfl

theorem coordDeriv_add {f q : Bulk → F} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hq : AnalyticAt ℝ q z) (i : Fin 5) :
    coordDeriv (fun y => f y + q y) i z = coordDeriv f i z + coordDeriv q i z := by
  unfold coordDeriv
  rw [fderiv_fun_add hf.differentiableAt hq.differentiableAt]
  rfl

theorem coordDeriv_sub {f q : Bulk → F} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hq : AnalyticAt ℝ q z) (i : Fin 5) :
    coordDeriv (fun y => f y - q y) i z = coordDeriv f i z - coordDeriv q i z := by
  unfold coordDeriv
  rw [fderiv_fun_sub hf.differentiableAt hq.differentiableAt]
  rfl

variable [CompleteSpace F]

theorem analyticAt_coordDeriv {f : Bulk → F} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (i : Fin 5) : AnalyticAt ℝ (coordDeriv f i) z := by
  exact ((ContinuousLinearMap.apply ℝ F (bulkBasis i)).analyticAt _).comp hf.fderiv

theorem coordDeriv_coordDeriv {f : Bulk → F} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (i j : Fin 5) :
    coordDeriv (coordDeriv f i) j z =
      fderiv ℝ (fderiv ℝ f) z (bulkBasis j) (bulkBasis i) := by
  let A : (Bulk →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (bulkBasis i)
  have hd := A.hasFDerivAt.comp z hf.fderiv.differentiableAt.hasFDerivAt
  have he : coordDeriv f i = fun y => A (fderiv ℝ f y) := rfl
  rw [he]
  unfold coordDeriv
  rw [hd.fderiv]
  rfl

theorem coordDeriv_commute {f : Bulk → F} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (i j : Fin 5) :
    coordDeriv (coordDeriv f i) j z = coordDeriv (coordDeriv f j) i z := by
  rw [coordDeriv_coordDeriv hf i j, coordDeriv_coordDeriv hf j i]
  exact (hf.contDiffAt (n := (2 : ℕ∞ω))).isSymmSndFDerivAt (by simp)
    (bulkBasis j) (bulkBasis i)

theorem coordDeriv_congr_germ {f q : Bulk → F} {z : Bulk}
    (h : f =ᶠ[𝓝 z] q) (i : Fin 5) : coordDeriv f i z = coordDeriv q i z := by
  unfold coordDeriv
  rw [h.fderiv_eq]

end CoordinateDerivatives

/-- Matrix commutator in the actual finite real matrix algebra. -/
def matrixCommutator (A B : BulkMatrix) : BulkMatrix := A * B - B * A

theorem matrixCommutator_skew (A B : BulkMatrix) :
    matrixCommutator A B = -matrixCommutator B A := by
  unfold matrixCommutator
  noncomm_ring

theorem matrixCommutator_jacobi (A B C : BulkMatrix) :
    matrixCommutator A (matrixCommutator B C) +
      matrixCommutator B (matrixCommutator C A) +
      matrixCommutator C (matrixCommutator A B) = 0 := by
  unfold matrixCommutator
  noncomm_ring

theorem coordDeriv_matrix_mul {f q : Bulk → BulkMatrix} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hq : AnalyticAt ℝ q z) (i : Fin 5) :
    coordDeriv (fun y => f y * q y) i z =
      coordDeriv f i z * q z + f z * coordDeriv q i z := by
  unfold coordDeriv
  rw [fderiv_fun_mul' hf.differentiableAt hq.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  ac_rfl

theorem analyticAt_matrixCommutator {f q : Bulk → BulkMatrix} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hq : AnalyticAt ℝ q z) :
    AnalyticAt ℝ (fun y => matrixCommutator (f y) (q y)) z :=
  (hf.mul hq).sub (hq.mul hf)

theorem coordDeriv_matrixCommutator {f q : Bulk → BulkMatrix} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hq : AnalyticAt ℝ q z) (i : Fin 5) :
    coordDeriv (fun y => matrixCommutator (f y) (q y)) i z =
      matrixCommutator (coordDeriv f i z) (q z) +
      matrixCommutator (f z) (coordDeriv q i z) := by
  change coordDeriv (fun y => f y * q y - q y * f y) i z = _
  rw [coordDeriv_sub (hf.mul hq) (hq.mul hf),
    coordDeriv_matrix_mul hf hq, coordDeriv_matrix_mul hq hf]
  unfold matrixCommutator
  noncomm_ring

/-- Curvature matrix of a coordinate connection; form indices are c,d. -/
def connectionCurvature (Γ : Fin 5 → Bulk → BulkMatrix) (z : Bulk)
    (c d : Fin 5) : BulkMatrix :=
  coordDeriv (Γ d) c z - coordDeriv (Γ c) d z +
    matrixCommutator (Γ c z) (Γ d z)

theorem analyticAt_connectionCurvature {Γ : Fin 5 → Bulk → BulkMatrix} {z : Bulk}
    (hΓ : ∀ i, AnalyticAt ℝ (Γ i) z) (c d : Fin 5) :
    AnalyticAt ℝ (fun y => connectionCurvature Γ y c d) z :=
  ((analyticAt_coordDeriv (hΓ d) c).sub (analyticAt_coordDeriv (hΓ c) d)).add
    (analyticAt_matrixCommutator (hΓ c) (hΓ d))

theorem coordDeriv_connectionCurvature {Γ : Fin 5 → Bulk → BulkMatrix} {z : Bulk}
    (hΓ : ∀ i, AnalyticAt ℝ (Γ i) z) (e c d : Fin 5) :
    coordDeriv (fun y => connectionCurvature Γ y c d) e z =
      (coordDeriv (coordDeriv (Γ d) c) e z -
        coordDeriv (coordDeriv (Γ c) d) e z) +
      (matrixCommutator (coordDeriv (Γ c) e z) (Γ d z) +
        matrixCommutator (Γ c z) (coordDeriv (Γ d) e z)) := by
  change coordDeriv
    (fun y => (coordDeriv (Γ d) c y - coordDeriv (Γ c) d y) +
      matrixCommutator (Γ c y) (Γ d y)) e z = _
  rw [coordDeriv_add
    ((analyticAt_coordDeriv (hΓ d) c).sub (analyticAt_coordDeriv (hΓ c) d))
    (analyticAt_matrixCommutator (hΓ c) (hΓ d))]
  rw [coordDeriv_sub (analyticAt_coordDeriv (hΓ d) c)
    (analyticAt_coordDeriv (hΓ c) d)]
  rw [coordDeriv_matrixCommutator (hΓ c) (hΓ d)]

/-- Endomorphism-valued differential Bianchi: the derivative and commutator
terms cancel by mixed-partial symmetry and associativity, for the actual
Frechet-derived curvature. No Bianchi premise is supplied. -/
theorem connection_differential_bianchi {Γ : Fin 5 → Bulk → BulkMatrix} {z : Bulk}
    (hΓ : ∀ i, AnalyticAt ℝ (Γ i) z) (e c d : Fin 5) :
    (coordDeriv (fun y => connectionCurvature Γ y c d) e z +
      matrixCommutator (Γ e z) (connectionCurvature Γ z c d)) +
    (coordDeriv (fun y => connectionCurvature Γ y d e) c z +
      matrixCommutator (Γ c z) (connectionCurvature Γ z d e)) +
    (coordDeriv (fun y => connectionCurvature Γ y e c) d z +
      matrixCommutator (Γ d z) (connectionCurvature Γ z e c)) = 0 := by
  rw [coordDeriv_connectionCurvature hΓ e c d,
    coordDeriv_connectionCurvature hΓ c d e,
    coordDeriv_connectionCurvature hΓ d e c]
  rw [coordDeriv_commute (hΓ d) c e,
    coordDeriv_commute (hΓ c) d e,
    coordDeriv_commute (hΓ e) d c]
  unfold connectionCurvature matrixCommutator
  noncomm_ring

end
end NSEGR.NativeLiterature
