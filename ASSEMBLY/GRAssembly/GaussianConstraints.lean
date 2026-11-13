import GRAdapter.GaussianCodazzi

/-!
GC16: actual Gaussian Ricci components. The tangential contraction below
uses the native total inverse and Frechet derivative and requires only local
nonsingularity. Flat-boundary transport to boundaryHamiltonian and
boundaryCodazzi remains a separate obligation; no such constraint is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open Filter
open scoped BigOperators Topology
noncomputable section

theorem bulkPartial_congr_of_eventuallyEq (f g : Bulk → ℝ) (z : Bulk)
    (h : f =ᶠ[𝓝 z] g) (i : Fin 5) : bulkPartial f i z = bulkPartial g i z := by
  unfold bulkPartial
  rw [h.fderiv_eq]

@[simp] theorem bulkPartial_neg (f : Bulk → ℝ) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun y => -f y) i z = -bulkPartial f i z := by
  simp [bulkPartial]

/-- The remaining lower-radial upper-radial symbol, including singular points. -/
theorem christoffel_gaussian_rbr_total (h : Bulk → Tensor4) (z : Bulk) (b : Fin 4) :
    christoffel (gaussianMetric h) z 0 b.succ 0 = 0 := by
  by_cases hh : IsUnit (h z).det
  · rw [christoffel, inverseMetric_gaussian h z hh, Fin.sum_univ_succ]
    simp only [gaussianMatrix_rr, gaussianMatrix_rb, bulkPartial_gaussian_rr,
      bulkPartial_gaussian_rb, bulkPartial_gaussian_ar, one_mul, zero_mul,
      zero_add, sub_zero, Finset.sum_const_zero, add_zero, mul_zero]
  · exact christoffel_gaussian_singular h z hh 0 b.succ 0

/-- The lower-radial upper-tangential symbol, including singular points. -/
theorem christoffel_gaussian_abr_total (h : Bulk → Tensor4) (z : Bulk) (a b : Fin 4) :
    christoffel (gaussianMetric h) z a.succ b.succ 0 = gaussianShapeOperator h z a b := by
  by_cases hh : IsUnit (h z).det
  · rw [christoffel, inverseMetric_gaussian h z hh, Fin.sum_univ_succ]
    simp only [gaussianMatrix_ar, gaussianMatrix_ab, bulkPartial_gaussian_rr,
      bulkPartial_gaussian_ar, bulkPartial_gaussian_rb, bulkPartial_gaussian_ab,
      zero_mul, zero_add, add_zero, sub_zero, gaussianShapeOperator, gaussianSecondForm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  · rw [christoffel_gaussian_singular h z hh,
      gaussianShapeOperator_singular h z hh]

/-- Locality suffices to differentiate Gamma^r_ab = -K_ab. -/
theorem radial_christoffel_derivative (h : Bulk → Tensor4) (z : Bulk)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (a b : Fin 4) (i : Fin 5) :
    bulkPartial (fun y => christoffel (gaussianMetric h) y 0 a.succ b.succ) i z =
      -bulkPartial (fun y => gaussianSecondForm h y a b) i z := by
  rw [← bulkPartial_neg]
  apply bulkPartial_congr_of_eventuallyEq
  filter_upwards [hN] with y hy
  exact christoffel_gaussian_rab h y hy a b

/-- Full tangential Ricci component after radial/tangential index separation.
Finite derivative sums are retained; no unproved trace differentiation is used. -/
def gaussianTangentialRicciComponent (h : Bulk → Tensor4) (z : Bulk)
    (a b : Fin 4) : ℝ :=
  (-bulkPartial (fun y => gaussianSecondForm h y a b) 0 z +
    ∑ c : Fin 4,
      (bulkPartial (fun y => gaussianTangentialChristoffel h y c a b) c.succ z -
       bulkPartial (fun y => gaussianTangentialChristoffel h y c a c) b.succ z)) +
  ((∑ d : Fin 4, gaussianSecondForm h z b d * gaussianShapeOperator h z d a) +
    ∑ c : Fin 4,
      (-(gaussianShapeOperator h z c c * gaussianSecondForm h z a b) +
        gaussianShapeOperator h z c b * gaussianSecondForm h z a c +
        ∑ d : Fin 4,
          (gaussianTangentialChristoffel h z c c d *
            gaussianTangentialChristoffel h z d a b -
           gaussianTangentialChristoffel h z c b d *
            gaussianTangentialChristoffel h z d a c)))

/-- Native Ricci, rather than an independently postulated curvature law. -/
theorem ricci_gaussian_tangential (h : Bulk → Tensor4) (z : Bulk)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (a b : Fin 4) :
    ricci (gaussianMetric h) z a.succ b.succ =
      gaussianTangentialRicciComponent h z a b := by
  have hz : IsUnit (h z).det := hN.self_of_nhds
  simp only [ricci, Fin.sum_univ_succ (n := 4),
    radial_christoffel_derivative h z hN,
    christoffel_gaussian_rr, christoffel_gaussian_rrb_total,
    christoffel_gaussian_rbr_total, christoffel_gaussian_shape,
    christoffel_gaussian_abr_total, christoffel_gaussian_abc_total,
    christoffel_gaussian_rab h z hz,
    bulkPartial_const, zero_mul, mul_zero, zero_sub, neg_zero, sub_zero,
    sub_self, zero_add, add_zero, Finset.sum_const_zero, neg_mul, mul_neg,
    sub_neg, neg_neg, gaussianTangentialRicciComponent]

/-- Vacuum annihilates the actual full tangential expression. -/
theorem gaussianTangentialRicciComponent_zero_of_vacuum
    (h : Bulk → Tensor4) (z : Bulk)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hv : ricci (gaussianMetric h) z = 0) (a b : Fin 4) :
    gaussianTangentialRicciComponent h z a b = 0 := by
  rw [← ricci_gaussian_tangential h z hN, hv]
  rfl

/-- All actual components: the converse uses the symmetric Ricci mixed entries
explicitly; it does not assert Ricci symmetry without its regularity hypotheses. -/
theorem gaussian_vacuum_iff_components (h : Bulk → Tensor4) (z : Bulk)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hMixed : ∀ a : Fin 4,
      ricci (gaussianMetric h) z a.succ 0 = ricci (gaussianMetric h) z 0 a.succ) :
    ricci (gaussianMetric h) z = 0 ↔
      gaussianNormalRicciComponent h z = 0 ∧
      (∀ a : Fin 4, gaussianCodazziComponent h z a = 0) ∧
      (∀ a b : Fin 4, gaussianTangentialRicciComponent h z a b = 0) := by
  constructor
  · intro hv
    exact ⟨gaussianNormalRicciComponent_zero_of_vacuum h z hv,
      gaussianCodazziComponent_zero_of_vacuum h z hv,
      gaussianTangentialRicciComponent_zero_of_vacuum h z hN hv⟩
  · rintro ⟨hn, hm, ht⟩
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · exact (ricci_gaussian_normal h z).trans hn
      · exact (ricci_gaussian_mixed h z b).trans (hm b)
    · refine Fin.cases ?_ (fun b => ?_) j
      · exact (hMixed a).trans ((ricci_gaussian_mixed h z a).trans (hm a))
      · exact (ricci_gaussian_tangential h z hN a b).trans (ht a b)

end
end NSEGR.Assembly
