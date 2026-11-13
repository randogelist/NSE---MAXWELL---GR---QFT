import GRAdapter.GaussianMetric
import ML056.Endpoint
import ML057.Endpoint
import ML058.Endpoint
import ML059.Endpoint
import ML060.Endpoint
import ML061.Endpoint
import ML063.Endpoint
import ML064.Endpoint

/-!
GC15: real matrix square roots, Schur complements, and the actual Gaussian
Lorentzian congruence. MatrixOrder supplies the positive-semidefinite order;
no CStar instance is inferred from the Frobenius matrix norm.
The quantitative collar-to-positive-spatial-block estimate is a separate edge.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open scoped BigOperators MatrixOrder
noncomputable section

/-- ML057--061,063--064: an actual invertible real Gram factor. -/
theorem positive_matrix_gram_factor {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Q.PosDef) :
    ∃ R : Matrix n n ℝ, IsUnit R.det ∧ R.transpose * R = Q := by
  let R := CFC.sqrt Q
  have hQ0 : 0 ≤ Q := GRTemp.ML058.endpoint.mpr hQ.posSemidef
  have hR0 : 0 ≤ R := GRTemp.ML059.endpoint Q
  have hRH : R.IsHermitian := (GRTemp.ML058.endpoint.mp hR0).isHermitian
  have hRT : R.transpose = R := by
    ext i j
    simpa only [Matrix.transpose_apply, star_trivial] using hRH.apply i j
  have hRU : IsUnit R :=
    (GRTemp.ML061.endpoint Q hQ0).mpr (GRTemp.ML057.endpoint hQ)
  refine ⟨R, (GRTemp.ML063.endpoint R).mp hRU, ?_⟩
  rw [hRT]
  exact GRTemp.ML060.endpoint Q hQ0

/-- The positive Schur complement in the timelike-first marking. -/
def lorentzSchur (α : ℝ) (b : Fin 3 → ℝ) (A : Tensor3) : Tensor3 :=
  A + α⁻¹ • Matrix.vecMulVec b b

theorem lorentzSchur_posDef (α : ℝ) (b : Fin 3 → ℝ) (A : Tensor3)
    (hα : 0 < α) (hA : A.PosDef) : (lorentzSchur α b A).PosDef := by
  apply GRTemp.ML056.endpoint hA
  have hb : (Matrix.vecMulVec b b).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star b
  exact hb.smul (inv_nonneg.mpr hα.le)

/-- Upper triangular C4; its spatial square is the Schur complement. -/
def lorentzTriangular (s : ℝ) (b : Fin 3 → ℝ) (R : Tensor3) : Tensor4 :=
  fun i j => Fin.cases
    (Fin.cases s (fun k : Fin 3 => -b k / s) j)
    (fun k : Fin 3 => Fin.cases 0 (fun l : Fin 3 => R k l) j) i

@[simp] theorem lorentzTriangular_00 (s : ℝ) (b : Fin 3 → ℝ) (R : Tensor3) :
    lorentzTriangular s b R 0 0 = s := rfl

@[simp] theorem lorentzTriangular_0j (s : ℝ) (b : Fin 3 → ℝ) (R : Tensor3)
    (j : Fin 3) : lorentzTriangular s b R 0 j.succ = -b j / s := rfl

@[simp] theorem lorentzTriangular_i0 (s : ℝ) (b : Fin 3 → ℝ) (R : Tensor3)
    (i : Fin 3) : lorentzTriangular s b R i.succ 0 = 0 := rfl

@[simp] theorem lorentzTriangular_ij (s : ℝ) (b : Fin 3 → ℝ) (R : Tensor3)
    (i j : Fin 3) : lorentzTriangular s b R i.succ j.succ = R i j := rfl

theorem lorentzTriangular_det (s : ℝ) (b : Fin 3 → ℝ) (R : Tensor3) :
    (lorentzTriangular s b R).det = s * R.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [lorentzTriangular_00, lorentzTriangular_i0, Fin.val_zero, pow_zero,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

theorem eta4_congruence_apply (C : Tensor4) (i j : Fin 4) :
    (C.transpose * eta4Matrix * C) i j =
      -C 0 i * C 0 j + ∑ k : Fin 3, C k.succ i * C k.succ j := by
  change (∑ k : Fin 4,
    (C.transpose * Matrix.diagonal lorentzSign4) i k * C k j) = _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [Fin.sum_univ_succ]
  simp [lorentzSign4]

/-- Exact Schur factorization; the hypotheses are finite matrix statements. -/
theorem lorentzTriangular_congruence (H : Tensor4) (s : ℝ)
    (R : Tensor3) (hs : s ≠ 0) (hsq : s * s = -H 0 0)
    (hH : ∀ i j, H i j = H j i)
    (hR : R.transpose * R =
      lorentzSchur (-H 0 0) (fun i : Fin 3 => H 0 i.succ)
        (fun i j : Fin 3 => H i.succ j.succ)) :
    H = (lorentzTriangular s (fun i : Fin 3 => H 0 i.succ) R).transpose *
      eta4Matrix * lorentzTriangular s (fun i : Fin 3 => H 0 i.succ) R := by
  ext i j
  rw [eta4_congruence_apply]
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · simp only [lorentzTriangular_00, lorentzTriangular_i0, zero_mul,
        Finset.sum_const_zero, add_zero]
      linarith
    · simp only [lorentzTriangular_00, lorentzTriangular_0j, lorentzTriangular_i0,
        lorentzTriangular_ij, zero_mul, Finset.sum_const_zero, add_zero]
      field_simp
  · refine Fin.cases ?_ (fun b => ?_) j
    · simp only [lorentzTriangular_00, lorentzTriangular_0j, lorentzTriangular_i0,
        lorentzTriangular_ij, mul_zero, Finset.sum_const_zero, add_zero]
      rw [hH a.succ 0]
      field_simp
    · simp only [lorentzTriangular_0j, lorentzTriangular_ij]
      have hRab := congr_fun (congr_fun hR a) b
      change (∑ k : Fin 3, R k a * R k b) =
        H a.succ b.succ + (-H 0 0)⁻¹ *
          (H 0 a.succ * H 0 b.succ) at hRab
      rw [hRab, ← hsq]
      field_simp
      <;> ring

/-- ML056--064 -> C4: negative time entry and positive spatial block suffice. -/
theorem lorentz_factor_of_spatial_posDef (H : Tensor4)
    (hH : ∀ i j, H i j = H j i) (ht : H 0 0 < 0)
    (hA : (fun i j : Fin 3 => H i.succ j.succ : Tensor3).PosDef) :
    ∃ C : Tensor4, IsUnit C.det ∧ H = C.transpose * eta4Matrix * C := by
  let α := -H 0 0
  have hα : 0 < α := neg_pos.mpr ht
  let b : Fin 3 → ℝ := fun i => H 0 i.succ
  let A : Tensor3 := fun i j => H i.succ j.succ
  obtain ⟨R, hRU, hR⟩ := positive_matrix_gram_factor (lorentzSchur α b A)
    (lorentzSchur_posDef α b A hα hA)
  let s := Real.sqrt α
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hα)
  have hsq : s * s = α := Real.mul_self_sqrt hα.le
  refine ⟨lorentzTriangular s b R, ?_, ?_⟩
  · rw [lorentzTriangular_det]
    exact (isUnit_iff_ne_zero.mpr hs).mul hRU
  · exact lorentzTriangular_congruence H s R hs hsq hH hR

/-- C4 -> diag(1,C4): the actual native five-dimensional Lorentzian predicate. -/
theorem gaussian_lorentzian_of_spatial_posDef (h : Bulk → Tensor4) (z : Bulk)
    (hs : ∀ i j, h z i j = h z j i) (ht : h z 0 0 < 0)
    (hA : (fun i j : Fin 3 => h z i.succ j.succ : Tensor3).PosDef) :
    LorentzianAt (gaussianMetric h) z := by
  obtain ⟨C, hC, hh⟩ := lorentz_factor_of_spatial_posDef (h z) hs ht hA
  exact gaussianMetric_lorentzian_of_congruence h z C hC hh

end
end NSEGR.Assembly
