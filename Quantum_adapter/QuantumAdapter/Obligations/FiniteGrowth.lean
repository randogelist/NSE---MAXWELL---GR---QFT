import QuantumAdapter.Obligations.ScalarGrowth

/-! Scalar integrating factors on the exact finite horizon. -/
set_option autoImplicit false
set_option Elab.async true
open Set
namespace QuantumAdapter.Obligations
noncomputable section

theorem scalar_constant_growth_on_Icc
    (y y' : ℝ → ℝ) (C T : ℝ) (hT : 0 ≤ T)
    (hy : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Icc (0:ℝ) T, y' t ≤ C*y t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    y t ≤ y 0 * Real.exp (C*t) := by
  have hw (s : ℝ) : HasDerivAt (fun r => Real.exp ((-C)*r)*y r)
      (Real.exp ((-C)*s)*(y' s-C*y s)) s := by
    have h := ((hasDerivAt_const_mul (x := s) (-C)).exp).fun_mul (hy s)
    have he : (Real.exp ((-C)*s)*(-C))*y s + Real.exp ((-C)*s)*y' s =
        Real.exp ((-C)*s)*(y' s-C*y s) := by ring
    rw [he] at h
    exact h
  have hc : Continuous (fun r => Real.exp ((-C)*r)*y r) :=
    continuous_iff_continuousAt.mpr (fun s => (hw s).continuousAt)
  have ha : AntitoneOn (fun r => Real.exp ((-C)*r)*y r) (Icc (0:ℝ) T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hc.continuousOn
      (fun s hs => (hw s).hasDerivWithinAt)
    intro s hs
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      (sub_nonpos.mpr (hineq s (interior_subset hs)))
  have hb := ha ⟨le_rfl,hT⟩ ht ht.1
  change Real.exp ((-C)*t)*y t ≤ Real.exp ((-C)*0)*y 0 at hb
  simp only [mul_zero, Real.exp_zero, one_mul] at hb
  calc
    y t = Real.exp (C*t)*(Real.exp ((-C)*t)*y t) := by
      rw [← mul_assoc, ← Real.exp_add]
      have he : C*t+(-C)*t=0 := by ring
      rw [he, Real.exp_zero, one_mul]
    _ ≤ Real.exp (C*t)*y 0 := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = y 0 * Real.exp (C*t) := mul_comm _ _

end
end QuantumAdapter.Obligations
