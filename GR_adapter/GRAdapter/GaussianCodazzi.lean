import GRAdapter.GaussianMetric

/-!
# Actual Gaussian mixed and normal Ricci contractions

The matrix determinant identifies both nonsingular and singular branches.
The Christoffel identities needed below consequently hold for the actual
total inverse and total Frechet derivative, without regularity hypotheses.
The mixed expression is the marked coordinate Codazzi contraction. Evaluation
at a flat induced boundary, and conversion to boundaryCodazzi, remain separate.
-/

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.Frobenius

namespace NSEGR
noncomputable section

theorem gaussianMatrix_det (H : Tensor4) : (gaussianMatrix H).det = H.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [gaussianMatrix_rr, gaussianMatrix_rb, Fin.val_zero, pow_zero,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

theorem inverseMetric_gaussian_singular (h : Bulk → Tensor4) (z : Bulk)
    (hs : ¬ IsUnit (h z).det) : inverseMetric (gaussianMetric h) z = 0 := by
  change (gaussianMatrix (h z))⁻¹ = 0
  apply Matrix.nonsing_inv_apply_not_isUnit
  simpa only [gaussianMatrix_det] using hs

theorem christoffel_gaussian_singular (h : Bulk → Tensor4) (z : Bulk)
    (hs : ¬ IsUnit (h z).det) (a b c : Fin 5) :
    christoffel (gaussianMetric h) z a b c = 0 := by
  rw [christoffel, inverseMetric_gaussian_singular h z hs]
  simp

/-- Actual tangential shape endomorphism h^{-1} K. -/
def gaussianShapeOperator (h : Bulk → Tensor4) (z : Bulk) : Tensor4 :=
  fun a b => ∑ c : Fin 4, (h z)⁻¹ a c * gaussianSecondForm h z c b

theorem gaussianShapeOperator_singular (h : Bulk → Tensor4) (z : Bulk)
    (hs : ¬ IsUnit (h z).det) (a b : Fin 4) :
    gaussianShapeOperator h z a b = 0 := by
  unfold gaussianShapeOperator
  rw [Matrix.nonsing_inv_apply_not_isUnit (h z) hs]
  simp

theorem gaussianTangentialChristoffel_singular (h : Bulk → Tensor4) (z : Bulk)
    (hs : ¬ IsUnit (h z).det) (a b c : Fin 4) :
    gaussianTangentialChristoffel h z a b c = 0 := by
  unfold gaussianTangentialChristoffel
  rw [Matrix.nonsing_inv_apply_not_isUnit (h z) hs]
  simp

/-- The upper-radial mixed connection vanishes also in the total singular branch. -/
theorem christoffel_gaussian_rrb_total (h : Bulk → Tensor4) (z : Bulk) (b : Fin 4) :
    christoffel (gaussianMetric h) z 0 0 b.succ = 0 := by
  by_cases hs : IsUnit (h z).det
  · exact christoffel_gaussian_rrb h z hs b
  · exact christoffel_gaussian_singular h z hs 0 0 b.succ

theorem christoffel_gaussian_shape (h : Bulk → Tensor4) (z : Bulk) (a b : Fin 4) :
    christoffel (gaussianMetric h) z a.succ 0 b.succ = gaussianShapeOperator h z a b := by
  by_cases hs : IsUnit (h z).det
  · exact christoffel_gaussian_arb h z hs a b
  · rw [christoffel_gaussian_singular h z hs,
      gaussianShapeOperator_singular h z hs]

theorem christoffel_gaussian_abc_total (h : Bulk → Tensor4) (z : Bulk) (a b c : Fin 4) :
    christoffel (gaussianMetric h) z a.succ b.succ c.succ =
      gaussianTangentialChristoffel h z a b c := by
  by_cases hs : IsUnit (h z).det
  · exact christoffel_gaussian_abc h z hs a b c
  · rw [christoffel_gaussian_singular h z hs,
      gaussianTangentialChristoffel_singular h z hs]

/-- The mixed Gaussian curvature expression written entirely in h, K, and the
intrinsic tangential connection. Derivatives of the trace remain separate sums;
no derivative-of-sum interchange is asserted without differentiability. -/
def gaussianCodazziComponent (h : Bulk → Tensor4) (z : Bulk) (a : Fin 4) : ℝ :=
  (∑ b : Fin 4,
    (bulkPartial (fun y => gaussianShapeOperator h y b a) b.succ z -
      bulkPartial (fun y => gaussianShapeOperator h y b b) a.succ z)) +
  (∑ b : Fin 4, ∑ c : Fin 4,
    (gaussianTangentialChristoffel h z b b c * gaussianShapeOperator h z c a -
      gaussianTangentialChristoffel h z b a c * gaussianShapeOperator h z c b))

/-- Native coordinate Codazzi contraction of the actual five-dimensional Ricci tensor. -/
theorem ricci_gaussian_mixed (h : Bulk → Tensor4) (z : Bulk) (a : Fin 4) :
    ricci (gaussianMetric h) z 0 a.succ = gaussianCodazziComponent h z a := by
  simp only [ricci, Fin.sum_univ_succ (n := 4), christoffel_gaussian_rr,
    christoffel_gaussian_rrb_total, christoffel_gaussian_shape,
    christoffel_gaussian_abc_total, bulkPartial_const, zero_mul, mul_zero,
    zero_sub, neg_zero, sub_zero, sub_self, zero_add, add_zero, Finset.sum_const_zero,
    gaussianCodazziComponent]

/-- Exact radial contraction before any interchange of derivative and trace. -/
def gaussianNormalRicciComponent (h : Bulk → Tensor4) (z : Bulk) : ℝ :=
  -(∑ a : Fin 4, bulkPartial (fun y => gaussianShapeOperator h y a a) 0 z) -
    ∑ a : Fin 4, ∑ b : Fin 4,
      gaussianShapeOperator h z a b * gaussianShapeOperator h z b a

theorem ricci_gaussian_normal (h : Bulk → Tensor4) (z : Bulk) :
    ricci (gaussianMetric h) z 0 0 = gaussianNormalRicciComponent h z := by
  simp only [ricci, Fin.sum_univ_succ (n := 4), christoffel_gaussian_rr,
    christoffel_gaussian_rrb_total, christoffel_gaussian_shape,
    bulkPartial_const, zero_mul, mul_zero, zero_sub, neg_zero, sub_zero, sub_self,
    zero_add, add_zero, Finset.sum_const_zero, Finset.sum_neg_distrib,
    gaussianNormalRicciComponent]
  ring

theorem gaussianCodazziComponent_zero_of_vacuum
    (h : Bulk → Tensor4) (z : Bulk) (hv : ricci (gaussianMetric h) z = 0) (a : Fin 4) :
    gaussianCodazziComponent h z a = 0 := by
  rw [← ricci_gaussian_mixed, hv]
  rfl

theorem gaussianNormalRicciComponent_zero_of_vacuum
    (h : Bulk → Tensor4) (z : Bulk) (hv : ricci (gaussianMetric h) z = 0) :
    gaussianNormalRicciComponent h z = 0 := by
  rw [← ricci_gaussian_normal, hv]
  rfl

end
end NSEGR
