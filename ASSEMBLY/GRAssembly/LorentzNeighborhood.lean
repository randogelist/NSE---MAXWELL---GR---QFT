import GRAssembly.LorentzFactor
import ML055.Endpoint

/-! GC15: explicit 1/12 coefficient neighborhood and the actual Lorentz factor. -/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open scoped BigOperators
noncomputable section

theorem small_entry_quadratic_bound (d x y : ℝ) (hd : |d| ≤ (1 / 12 : ℝ)) :
    |x * d * y| ≤ (1 / 24 : ℝ) * (x ^ 2 + y ^ 2) := by
  calc
    |x * d * y| = |d| * (|x| * |y|) := by simp only [abs_mul]; ring
    _ ≤ (1 / 12 : ℝ) * (|x| * |y|) :=
      mul_le_mul_of_nonneg_right hd (mul_nonneg (abs_nonneg x) (abs_nonneg y))
    _ ≤ (1 / 24 : ℝ) * (x ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

theorem spatial_quadratic_error_bound (A : Tensor3)
    (hA : ∀ i j : Fin 3, |A i j - (1 : Tensor3) i j| ≤ (1 / 12 : ℝ))
    (x : Fin 3 → ℝ) :
    |∑ i : Fin 3, ∑ j : Fin 3, x i * (A i j - (1 : Tensor3) i j) * x j| ≤
      (1 / 4 : ℝ) * ∑ i : Fin 3, (x i) ^ 2 := by
  calc
    |∑ i : Fin 3, ∑ j : Fin 3, x i * (A i j - (1 : Tensor3) i j) * x j| ≤
        ∑ i : Fin 3, |∑ j : Fin 3, x i * (A i j - (1 : Tensor3) i j) * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        |x i * (A i j - (1 : Tensor3) i j) * x j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        (1 / 24 : ℝ) * ((x i) ^ 2 + (x j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact small_entry_quadratic_bound _ _ _ (hA i j)
    _ = (1 / 4 : ℝ) * ∑ i : Fin 3, (x i) ^ 2 := by
      simp [Fin.sum_univ_succ]
      <;> ring

/-- The spatial block is bounded below by three quarters of the identity. -/
theorem spatial_posDef_of_near_identity (A : Tensor3)
    (hs : ∀ i j, A i j = A j i)
    (hA : ∀ i j : Fin 3, |A i j - (1 : Tensor3) i j| ≤ (1 / 12 : ℝ)) :
    A.PosDef := by
  apply GRTemp.ML055.endpoint
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hs j i
  · intro x hx
    have hnonzero : ∃ i : Fin 3, x i ≠ 0 := by
      by_contra hn
      apply hx
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hnonzero
    have hsum : 0 < ∑ j : Fin 3, (x j) ^ 2 := by
      apply lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      exact Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
    have he := (abs_le.mp (spatial_quadratic_error_bound A hA x)).1
    have hid : star x ⬝ᵥ (A *ᵥ x) = (∑ j : Fin 3, (x j) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3,
          x i * (A i j - (1 : Tensor3) i j) * x j := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.one_apply]
      <;> ring
    rw [hid]
    linarith

/-- Explicit pointwise inertia certificate from all sixteen entry bounds. -/
theorem lorentz_factor_of_near_eta4 (H : Tensor4)
    (hs : ∀ i j, H i j = H j i)
    (hclose : ∀ i j : Fin 4, |H i j - eta4 i j| < (1 / 12 : ℝ)) :
    ∃ C : Tensor4, IsUnit C.det ∧ H = C.transpose * eta4Matrix * C := by
  apply lorentz_factor_of_spatial_posDef H hs
  · have ht := (abs_lt.mp (hclose 0 0)).2
    norm_num [eta4, lorentzSign4] at ht
    linarith
  · apply spatial_posDef_of_near_identity
    · intro i j
      exact hs i.succ j.succ
    · intro i j
      simpa [eta4, lorentzSign4, Matrix.one_apply] using (hclose i.succ j.succ).le

theorem gaussian_lorentzian_of_near_eta4 (h : Bulk → Tensor4) (z : Bulk)
    (hs : ∀ i j, h z i j = h z j i)
    (hclose : ∀ i j : Fin 4, |h z i j - eta4 i j| < (1 / 12 : ℝ)) :
    LorentzianAt (gaussianMetric h) z := by
  obtain ⟨C, hC, hH⟩ := lorentz_factor_of_near_eta4 (h z) hs hclose
  exact gaussianMetric_lorentzian_of_congruence h z C hC hH

end
end NSEGR.Assembly
