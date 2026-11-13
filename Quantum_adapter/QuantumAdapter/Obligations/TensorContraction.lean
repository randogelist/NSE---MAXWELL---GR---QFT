import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Pointwise Hilbert-tensor estimates for the periodic interpolation identity

No symmetry of the second derivative tensor is required.  The index set of
spatial directions is `Fin 3`; the target may be any real inner-product space.
-/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace QuantumAdapter.Obligations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem real_inner_sq_le_norm_sq_mul (x y : E) :
    (inner ℝ x y) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg (inner ℝ x y))
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))).2 (abs_real_inner_le_norm x y)
  simpa only [sq_abs, mul_pow] using h

theorem tensor_row_inner_sq_le (g h : Fin 3 → E) :
    (∑ j, inner ℝ (g j) (h j)) ^ 2 ≤
      (∑ j, ‖g j‖ ^ 2) * ∑ j, ‖h j‖ ^ 2 := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => sq_nonneg ‖g j‖) (fun j _ => sq_nonneg ‖h j‖)
    (fun j _ => real_inner_sq_le_norm_sq_mul (g j) (h j))

/-- The cubic gradient/Hessian contraction, with constant exactly one. -/
theorem tensor_gradient_hessian_contraction
    (f : E) (g : Fin 3 → E) (H : Fin 3 → Fin 3 → E) :
    |∑ j, inner ℝ f (g j) * (∑ l, inner ℝ (g l) (H j l))| ≤
      ‖f‖ * (∑ j, ‖g j‖ ^ 2) * Real.sqrt (∑ j, ∑ l, ‖H j l‖ ^ 2) := by
  let G : ℝ := ∑ j, ‖g j‖ ^ 2
  let D : ℝ := ∑ j, ∑ l, ‖H j l‖ ^ 2
  let a : Fin 3 → ℝ := fun j => inner ℝ f (g j)
  let b : Fin 3 → ℝ := fun j => ∑ l, inner ℝ (g l) (H j l)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun j _ => sq_nonneg ‖g j‖)
  have hD : 0 ≤ D :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖H j l‖))
  have ha : (∑ j, a j ^ 2) ≤ ‖f‖ ^ 2 * G := by
    calc
      (∑ j, a j ^ 2) ≤ ∑ j, ‖f‖ ^ 2 * ‖g j‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => real_inner_sq_le_norm_sq_mul f (g j))
      _ = ‖f‖ ^ 2 * G := by simp only [G, Finset.mul_sum]
  have hb : (∑ j, b j ^ 2) ≤ G * D := by
    calc
      (∑ j, b j ^ 2) ≤ ∑ j, G * (∑ l, ‖H j l‖ ^ 2) :=
        Finset.sum_le_sum (fun j _ => tensor_row_inner_sq_le g (H j))
      _ = G * D := by simp only [D, Finset.mul_sum]
  have hs : (∑ j, a j * b j) ^ 2 ≤ (‖f‖ * G * Real.sqrt D) ^ 2 := by
    calc
      (∑ j, a j * b j) ^ 2 ≤ (∑ j, a j ^ 2) * ∑ j, b j ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
      _ ≤ (‖f‖ ^ 2 * G) * (G * D) :=
        mul_le_mul ha hb (Finset.sum_nonneg (fun j _ => sq_nonneg (b j)))
          (mul_nonneg (sq_nonneg ‖f‖) hG)
      _ = (‖f‖ * G * Real.sqrt D) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hD]
        ring
  have hn : 0 ≤ ‖f‖ * G * Real.sqrt D :=
    mul_nonneg (mul_nonneg (norm_nonneg f) hG) (Real.sqrt_nonneg D)
  have habs : |∑ j, a j * b j| ≤ ‖f‖ * G * Real.sqrt D :=
    (sq_le_sq₀ (abs_nonneg _) hn).mp (by simpa only [sq_abs] using hs)
  exact habs

/-- Three diagonal entries are bounded by twice the full Frobenius norm. -/
theorem tensor_diagonal_norm_sum_le (H : Fin 3 → Fin 3 → E) :
    (∑ j, ‖H j j‖) ≤ 2 * Real.sqrt (∑ j, ∑ l, ‖H j l‖ ^ 2) := by
  let D : ℝ := ∑ j, ∑ l, ‖H j l‖ ^ 2
  have hD : 0 ≤ D :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖H j l‖))
  have hd : (∑ j, ‖H j j‖ ^ 2) ≤ D := by
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.single_le_sum (fun l _ => sq_nonneg ‖H j l‖) (Finset.mem_univ j)
  have hcs : (∑ j, ‖H j j‖) ^ 2 ≤ 3 * (∑ j, ‖H j j‖ ^ 2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin 3 => (1 : ℝ)) (fun j => ‖H j j‖)
  have hsqrt := Real.sq_sqrt hD
  have hs : (∑ j, ‖H j j‖) ^ 2 ≤ (2 * Real.sqrt D) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun j _ => norm_nonneg (H j j)))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg D))).mp hs

theorem tensor_trace_inner_bound (f : E) (H : Fin 3 → Fin 3 → E) :
    |∑ j, inner ℝ f (H j j)| ≤
      2 * ‖f‖ * Real.sqrt (∑ j, ∑ l, ‖H j l‖ ^ 2) := by
  calc
    |∑ j, inner ℝ f (H j j)| ≤ ∑ j, |inner ℝ f (H j j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖f‖ * ‖H j j‖ :=
      Finset.sum_le_sum (fun j _ => abs_real_inner_le_norm f (H j j))
    _ = ‖f‖ * (∑ j, ‖H j j‖) := by rw [Finset.mul_sum]
    _ ≤ ‖f‖ * (2 * Real.sqrt (∑ j, ∑ l, ‖H j l‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (tensor_diagonal_norm_sum_le H) (norm_nonneg f)
    _ = 2 * ‖f‖ * Real.sqrt (∑ j, ∑ l, ‖H j l‖ ^ 2) := by ring

/-- Exact pointwise estimate for the derivative terms produced by periodic IBP. -/
theorem tensor_interpolation_integrand_bound
    (f : E) (g : Fin 3 → E) (H : Fin 3 → Fin 3 → E) :
    |(∑ j, inner ℝ f (H j j)) * (∑ j, ‖g j‖ ^ 2) +
      2 * (∑ j, inner ℝ f (g j) * (∑ l, inner ℝ (g l) (H j l)))| ≤
      4 * ‖f‖ * (∑ j, ‖g j‖ ^ 2) * Real.sqrt (∑ j, ∑ l, ‖H j l‖ ^ 2) := by
  let G : ℝ := ∑ j, ‖g j‖ ^ 2
  let D : ℝ := ∑ j, ∑ l, ‖H j l‖ ^ 2
  let T : ℝ := ∑ j, inner ℝ f (H j j)
  let C : ℝ := ∑ j, inner ℝ f (g j) * (∑ l, inner ℝ (g l) (H j l))
  have hG : 0 ≤ G := Finset.sum_nonneg (fun j _ => sq_nonneg ‖g j‖)
  have hT : |T| ≤ 2 * ‖f‖ * Real.sqrt D := tensor_trace_inner_bound f H
  have hC : |C| ≤ ‖f‖ * G * Real.sqrt D := tensor_gradient_hessian_contraction f g H
  change |T * G + 2 * C| ≤ 4 * ‖f‖ * G * Real.sqrt D
  calc
    |T * G + 2 * C| ≤ |T * G| + |2 * C| := abs_add_le _ _
    _ = |T| * G + 2 * |C| := by rw [abs_mul, abs_mul, abs_of_nonneg hG]; norm_num
    _ ≤ (2 * ‖f‖ * Real.sqrt D) * G + 2 * (‖f‖ * G * Real.sqrt D) :=
      add_le_add (mul_le_mul_of_nonneg_right hT hG)
        (mul_le_mul_of_nonneg_left hC (by norm_num))
    _ = 4 * ‖f‖ * G * Real.sqrt D := by ring

end QuantumAdapter.Obligations
