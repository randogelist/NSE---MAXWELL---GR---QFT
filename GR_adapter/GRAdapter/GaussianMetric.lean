import GRAdapter.Boundary

/-!
# Native Gaussian block geometry

All matrices, inverses, coordinate derivatives and Christoffel symbols below
are the actual objects of Geometry.lean. No curvature identity or vacuum
extension theorem is assumed. Differentiability is unnecessary for these
identities because the same total Fréchet derivative occurs on both sides.
-/

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.Frobenius

namespace NSEGR
noncomputable section

/-- The exact matrix `diag(1,H)` in the fixed radial-first marking. -/
def gaussianMatrix (H : Tensor4) : BulkMatrix := fun a b =>
  Fin.cases (Fin.cases (1 : ℝ) (fun _ : Fin 4 => 0) b)
    (fun i : Fin 4 => Fin.cases 0 (fun j : Fin 4 => H i j) b) a

@[simp] theorem gaussianMatrix_rr (H : Tensor4) : gaussianMatrix H 0 0 = 1 := rfl

@[simp] theorem gaussianMatrix_rb (H : Tensor4) (b : Fin 4) :
    gaussianMatrix H 0 b.succ = 0 := rfl

@[simp] theorem gaussianMatrix_ar (H : Tensor4) (a : Fin 4) :
    gaussianMatrix H a.succ 0 = 0 := rfl

@[simp] theorem gaussianMatrix_ab (H : Tensor4) (a b : Fin 4) :
    gaussianMatrix H a.succ b.succ = H a b := rfl

@[simp] theorem gaussianMatrix_one : gaussianMatrix (1 : Tensor4) = 1 := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · rfl
    · change (0 : ℝ) = (1 : BulkMatrix) 0 j.succ
      exact (Matrix.one_apply_ne (Ne.symm (Fin.succ_ne_zero j))).symm
  · refine Fin.cases ?_ (fun j => ?_) b
    · change (0 : ℝ) = (1 : BulkMatrix) i.succ 0
      exact (Matrix.one_apply_ne (Fin.succ_ne_zero i)).symm
    · change (1 : Tensor4) i j = (1 : BulkMatrix) i.succ j.succ
      simp [Matrix.one_apply]

theorem gaussianMatrix_mul (A B : Tensor4) :
    gaussianMatrix A * gaussianMatrix B = gaussianMatrix (A * B) := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · change (∑ k : Fin 5, gaussianMatrix A 0 k * gaussianMatrix B k 0) = 1
      rw [Fin.sum_univ_succ]
      simp only [gaussianMatrix_rr, gaussianMatrix_rb, gaussianMatrix_ar,
        one_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · change (∑ k : Fin 5, gaussianMatrix A 0 k * gaussianMatrix B k j.succ) = 0
      rw [Fin.sum_univ_succ]
      simp only [gaussianMatrix_rr, gaussianMatrix_rb, gaussianMatrix_ar,
        gaussianMatrix_ab, one_mul, zero_mul, Finset.sum_const_zero, add_zero]
  · refine Fin.cases ?_ (fun j => ?_) b
    · change (∑ k : Fin 5, gaussianMatrix A i.succ k * gaussianMatrix B k 0) = 0
      rw [Fin.sum_univ_succ]
      simp only [gaussianMatrix_rr, gaussianMatrix_rb, gaussianMatrix_ar,
        gaussianMatrix_ab, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
    · change (∑ k : Fin 5, gaussianMatrix A i.succ k * gaussianMatrix B k j.succ) =
        ∑ k : Fin 4, A i k * B k j
      rw [Fin.sum_univ_succ]
      simp only [gaussianMatrix_rb, gaussianMatrix_ar, gaussianMatrix_ab,
        zero_mul, zero_add]

theorem gaussianMatrix_transpose (A : Tensor4) :
    gaussianMatrix A.transpose = (gaussianMatrix A).transpose := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b <;> rfl
  · refine Fin.cases ?_ (fun j => ?_) b <;> rfl

theorem gaussianMatrix_isUnit_det (A : Tensor4) (hA : IsUnit A.det) :
    IsUnit (gaussianMatrix A).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := gaussianMatrix A⁻¹)
  rw [gaussianMatrix_mul, Matrix.mul_nonsing_inv A hA, gaussianMatrix_one]

theorem gaussianMatrix_inverse (A : Tensor4) (hA : IsUnit A.det) :
    (gaussianMatrix A)⁻¹ = gaussianMatrix A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [gaussianMatrix_mul, Matrix.mul_nonsing_inv A hA, gaussianMatrix_one]

@[simp] theorem gaussianMatrix_eta4 : gaussianMatrix eta4 = eta5 := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · norm_num [eta5, gaussianMatrix]
    · change (0 : ℝ) = eta5 0 j.succ
      simp [eta5, Matrix.diagonal_apply]
  · refine Fin.cases ?_ (fun j => ?_) b
    · change (0 : ℝ) = eta5 i.succ 0
      simp [eta5, Matrix.diagonal_apply]
    · change eta4 i j = eta5 i.succ j.succ
      have hi : (i.succ = (1 : Fin 5)) ↔ i = 0 := by
        change (i.succ = (0 : Fin 4).succ) ↔ i = 0
        exact Fin.succ_inj
      simp [eta4, eta5, Matrix.diagonal_apply, lorentzSign4, hi]

/-- A global coefficient field with the exact Gaussian radial row and column. -/
def gaussianMetric (h : Bulk → Tensor4) : Metric := fun z => gaussianMatrix (h z)

@[simp] theorem gaussianMetric_rr (h : Bulk → Tensor4) (z : Bulk) :
    gaussianMetric h z 0 0 = 1 := rfl

@[simp] theorem gaussianMetric_rb (h : Bulk → Tensor4) (z : Bulk) (b : Fin 4) :
    gaussianMetric h z 0 b.succ = 0 := rfl

@[simp] theorem gaussianMetric_ar (h : Bulk → Tensor4) (z : Bulk) (a : Fin 4) :
    gaussianMetric h z a.succ 0 = 0 := rfl

@[simp] theorem gaussianMetric_ab (h : Bulk → Tensor4) (z : Bulk) (a b : Fin 4) :
    gaussianMetric h z a.succ b.succ = h z a b := rfl

theorem inverseMetric_gaussian (h : Bulk → Tensor4) (z : Bulk)
    (hh : IsUnit (h z).det) :
    inverseMetric (gaussianMetric h) z = gaussianMatrix ((h z)⁻¹) :=
  gaussianMatrix_inverse (h z) hh

/-- Lifting an explicit tangential Lorentz factor is actual bulk congruence. -/
theorem gaussianMetric_lorentzian_of_congruence
    (h : Bulk → Tensor4) (z : Bulk) (C : Tensor4)
    (hC : IsUnit C.det) (hh : h z = C.transpose * (eta4 : Tensor4) * C) :
    LorentzianAt (gaussianMetric h) z := by
  refine ⟨gaussianMatrix C, gaussianMatrix_isUnit_det C hC, ?_⟩
  change gaussianMatrix (h z) = (gaussianMatrix C).transpose * eta5 * gaussianMatrix C
  rw [hh, ← gaussianMatrix_transpose, ← gaussianMatrix_eta4,
    gaussianMatrix_mul, gaussianMatrix_mul]

@[simp] theorem bulkPartial_gaussian_rr
    (h : Bulk → Tensor4) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun y => gaussianMetric h y 0 0) i z = 0 := by
  change bulkPartial (fun _ : Bulk => (1 : ℝ)) i z = 0
  exact bulkPartial_const 1 i z

@[simp] theorem bulkPartial_gaussian_rb
    (h : Bulk → Tensor4) (b : Fin 4) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun y => gaussianMetric h y 0 b.succ) i z = 0 := by
  change bulkPartial (fun _ : Bulk => (0 : ℝ)) i z = 0
  exact bulkPartial_const 0 i z

@[simp] theorem bulkPartial_gaussian_ar
    (h : Bulk → Tensor4) (a : Fin 4) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun y => gaussianMetric h y a.succ 0) i z = 0 := by
  change bulkPartial (fun _ : Bulk => (0 : ℝ)) i z = 0
  exact bulkPartial_const 0 i z

@[simp] theorem bulkPartial_gaussian_ab
    (h : Bulk → Tensor4) (a b : Fin 4) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun y => gaussianMetric h y a.succ b.succ) i z =
      bulkPartial (fun y => h y a b) i z := rfl

/-- The actual Gaussian normal second fundamental form on each radial slice. -/
def gaussianSecondForm (h : Bulk → Tensor4) (z : Bulk) : Tensor4 :=
  fun a b => (1 / 2 : ℝ) * bulkPartial (fun y => h y a b) 0 z

theorem boundaryK_gaussian (h : Bulk → Tensor4) (t : ℝ) (x : Vec) :
    boundaryK (gaussianMetric h) t x = gaussianSecondForm h (bulkPoint 0 t x) := rfl

/-- Every upper-index Christoffel symbol with two radial lower indices vanishes. -/
theorem christoffel_gaussian_rr (h : Bulk → Tensor4) (z : Bulk) (a : Fin 5) :
    christoffel (gaussianMetric h) z a 0 0 = 0 := by
  rw [christoffel, Fin.sum_univ_succ]
  simp only [bulkPartial_gaussian_rr,
    bulkPartial_gaussian_ar, zero_add, sub_zero, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- Exact upper-radial tangential Christoffel component: Gamma^r_ab=-K_ab. -/
theorem christoffel_gaussian_rab (h : Bulk → Tensor4) (z : Bulk)
    (hh : IsUnit (h z).det) (a b : Fin 4) :
    christoffel (gaussianMetric h) z 0 a.succ b.succ = -gaussianSecondForm h z a b := by
  rw [christoffel, inverseMetric_gaussian h z hh, Fin.sum_univ_succ]
  simp only [gaussianMatrix_rr, gaussianMatrix_rb, bulkPartial_gaussian_rb,
    bulkPartial_gaussian_ab, zero_add, zero_sub, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero, gaussianSecondForm]
  ring

/-- Exact upper-radial mixed Christoffel component. -/
theorem christoffel_gaussian_rrb (h : Bulk → Tensor4) (z : Bulk)
    (hh : IsUnit (h z).det) (b : Fin 4) :
    christoffel (gaussianMetric h) z 0 0 b.succ = 0 := by
  rw [christoffel, inverseMetric_gaussian h z hh, Fin.sum_univ_succ]
  simp only [gaussianMatrix_rr, gaussianMatrix_rb, bulkPartial_gaussian_rr,
    bulkPartial_gaussian_rb, one_mul, zero_mul, zero_add, sub_zero,
    Finset.sum_const_zero, add_zero, mul_zero]

/-- Exact upper-tangential mixed component: Gamma^a_rb=h^{ac}K_cb. -/
theorem christoffel_gaussian_arb (h : Bulk → Tensor4) (z : Bulk)
    (hh : IsUnit (h z).det) (a b : Fin 4) :
    christoffel (gaussianMetric h) z a.succ 0 b.succ =
      ∑ c : Fin 4, (h z)⁻¹ a c * gaussianSecondForm h z c b := by
  rw [christoffel, inverseMetric_gaussian h z hh, Fin.sum_univ_succ]
  simp only [gaussianMatrix_ar, gaussianMatrix_ab, bulkPartial_gaussian_ar,
    bulkPartial_gaussian_rb, bulkPartial_gaussian_ab, zero_mul, zero_add,
    add_zero, sub_zero, gaussianSecondForm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- Intrinsic tangential connection, written with the actual marked bulk derivatives. -/
def gaussianTangentialChristoffel (h : Bulk → Tensor4) (z : Bulk)
    (a b c : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin 4, (h z)⁻¹ a d *
    (bulkPartial (fun y => h y d c) b.succ z +
      bulkPartial (fun y => h y d b) c.succ z -
      bulkPartial (fun y => h y b c) d.succ z)

theorem christoffel_gaussian_abc (h : Bulk → Tensor4) (z : Bulk)
    (hh : IsUnit (h z).det) (a b c : Fin 4) :
    christoffel (gaussianMetric h) z a.succ b.succ c.succ =
      gaussianTangentialChristoffel h z a b c := by
  rw [christoffel, inverseMetric_gaussian h z hh, Fin.sum_univ_succ]
  simp only [gaussianMatrix_ar, gaussianMatrix_ab, bulkPartial_gaussian_ab,
    zero_mul, zero_add, gaussianTangentialChristoffel]

end
end NSEGR
