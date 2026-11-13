import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Scalar integrating factors for the exact relative and tame energy estimates.
The derivative inequality is explicit; this file alone does not establish
the native Navier--Stokes differential inequalities.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory

namespace QuantumAdapter.Obligations

noncomputable section

/-- Variable-coefficient scalar Gronwall without division by the energy. -/
theorem scalar_growth_bound
    (y y' g : ℝ → ℝ) (hg : Continuous g)
    (hy : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t, 0 ≤ t → y' t ≤ g t * y t)
    {t : ℝ} (ht : 0 ≤ t) :
    y t ≤ y 0 * Real.exp (∫ s in (0 : ℝ)..t, g s) := by
  let K : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s
  have hK (s : ℝ) : HasDerivAt K (g s) s :=
    (hg.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hw (s : ℝ) : HasDerivAt
      (fun r => Real.exp (-K r) * y r)
      (Real.exp (-K s) * (y' s - g s * y s)) s := by
    have h := ((hK s).neg.exp).fun_mul (hy s)
    simp only [Pi.neg_apply] at h
    have he : (Real.exp (-K s) * (-g s)) * y s +
        Real.exp (-K s) * y' s =
        Real.exp (-K s) * (y' s - g s * y s) := by ring
    rw [he] at h
    exact h
  have hc : Continuous (fun r => Real.exp (-K r) * y r) :=
    continuous_iff_continuousAt.mpr (fun s => (hw s).continuousAt)
  have ha : AntitoneOn (fun r => Real.exp (-K r) * y r) (Ici (0 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hc.continuousOn
      (fun s _ => (hw s).hasDerivWithinAt)
    intro s hs
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    exact sub_nonpos.mpr (hineq s (interior_subset hs))
  have hb := ha (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp) ht ht
  change Real.exp (-K t) * y t ≤ Real.exp (-K 0) * y 0 at hb
  have hK0 : K 0 = 0 := by simp [K]
  rw [hK0, neg_zero, Real.exp_zero, one_mul] at hb
  calc
    y t = Real.exp (K t) * (Real.exp (-K t) * y t) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (K t) * y 0 :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = y 0 * Real.exp (∫ s in (0 : ℝ)..t, g s) := mul_comm _ _

/-- Exact square-root growth; the prefactor is one, including zero energy. -/
theorem sqrt_energy_growth_bound
    (y y' g : ℝ → ℝ) (C : ℝ) (hg : Continuous g)
    (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy_nonneg : ∀ t, 0 ≤ t → 0 ≤ y t)
    (hineq : ∀ t, 0 ≤ t → y' t ≤ (2 * C) * g t * y t)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (y t) ≤ Real.sqrt (y 0) *
      Real.exp (C * ∫ s in (0 : ℝ)..t, g s) := by
  have hb := scalar_growth_bound y y' (fun s => (2 * C) * g s)
    (hg.const_mul _) hy (fun s hs => hineq s hs) ht
  rw [intervalIntegral.integral_const_mul] at hb
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg
    (Real.sqrt_nonneg _) (Real.exp_nonneg _))).1
  rw [Real.sq_sqrt (hy_nonneg t ht), mul_pow,
    Real.sq_sqrt (hy_nonneg 0 le_rfl)]
  have he : (Real.exp (C * ∫ s in (0 : ℝ)..t, g s)) ^ 2 =
      Real.exp ((2 * C) * ∫ s in (0 : ℝ)..t, g s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact hb

end

end QuantumAdapter.Obligations
