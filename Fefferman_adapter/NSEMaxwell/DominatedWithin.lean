import NSEMaxwell.Classical

/-!
# Differentiation under an integral within a time domain

The derivative is a `HasDerivWithinAt`, so the theorem includes the right
derivative at the initial time. The derivative field's integrability is an
explicit hypothesis; no derivative-norm estimate is inferred from an arbitrary
restricted domain. The proof is dominated convergence for the normalized
first-order remainder.
-/

set_option autoImplicit false

namespace NSEMaxwell.DominatedWithin

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {F : ℝ → α → E} {F' : α → E}
  {s : Set ℝ} {t : ℝ} {bound : α → ℝ}

/-- Dominated differentiation with the exact one-sided or restricted derivative. -/
theorem hasDerivWithinAt_integral_of_dominated
    (hF_int : ∀ᶠ r in 𝓝[s] t, Integrable (F r) μ)
    (hF_base : Integrable (F t) μ)
    (hF'_int : Integrable F' μ)
    (h_bound : ∀ᶠ r in 𝓝[s] t, ∀ᵐ a ∂μ,
      ‖F r a - F t a‖ ≤ bound a * ‖r - t‖)
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivWithinAt (fun r => F r a) (F' a) s t) :
    HasDerivWithinAt (fun r => ∫ a, F r a ∂μ) (∫ a, F' a ∂μ) s t := by
  have nneg (r : ℝ) : 0 ≤ ‖r - t‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have h_bound_abs : ∀ᶠ r in 𝓝[s] t, ∀ᵐ a ∂μ,
      ‖F r a - F t a‖ ≤ |bound a| * ‖r - t‖ := by
    filter_upwards [h_bound] with r hr
    exact hr.mono fun a ha =>
      ha.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have h_remainder : ∀ᶠ r in 𝓝[s] t,
      ‖r - t‖⁻¹ *
          ‖((∫ a, F r a ∂μ) - ∫ a, F t a ∂μ) - (r - t) • (∫ a, F' a ∂μ)‖ =
        ‖∫ a, ‖r - t‖⁻¹ • (F r a - F t a - (r - t) • F' a) ∂μ‖ := by
    filter_upwards [hF_int] with r hr
    have hi :
        (∫ a, ‖r - t‖⁻¹ • (F r a - F t a - (r - t) • F' a) ∂μ) =
          ‖r - t‖⁻¹ •
            (((∫ a, F r a ∂μ) - ∫ a, F t a ∂μ) - (r - t) • (∫ a, F' a ∂μ)) := by
      have hsplit := integral_sub (hr.sub hF_base) (hF'_int.smul (r - t))
      simp only [Pi.sub_apply, Pi.smul_apply] at hsplit
      rw [integral_smul, hsplit, integral_sub hr hF_base, integral_smul]
    rw [hi, norm_smul_of_nonneg (nneg r)]
  rw [hasDerivWithinAt_iff_tendsto, tendsto_congr' h_remainder,
    ← tendsto_zero_iff_norm_tendsto_zero]
  have hz : (∫ a : α, (0 : E) ∂μ) = 0 := by simp
  rw [← hz]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun a => |bound a| + ‖F' a‖)
  · filter_upwards [hF_int] with r hr
    apply AEStronglyMeasurable.const_smul
    exact ((hr.aestronglyMeasurable.sub hF_base.aestronglyMeasurable).sub
      (hF'_int.aestronglyMeasurable.const_smul (r - t)))
  · filter_upwards [h_bound_abs] with r hr
    apply hr.mono
    intro a ha
    calc
      ‖‖r - t‖⁻¹ • (F r a - F t a - (r - t) • F' a)‖ =
          ‖‖r - t‖⁻¹ • (F r a - F t a) -
            ‖r - t‖⁻¹ • ((r - t) • F' a)‖ := by rw [smul_sub]
      _ ≤ ‖‖r - t‖⁻¹ • (F r a - F t a)‖ +
          ‖‖r - t‖⁻¹ • ((r - t) • F' a)‖ := norm_sub_le _ _
      _ = ‖r - t‖⁻¹ * ‖F r a - F t a‖ +
          ‖r - t‖⁻¹ * (‖F' a‖ * ‖r - t‖) := by
        rw [norm_smul_of_nonneg (nneg r), norm_smul_of_nonneg (nneg r), norm_smul]
        ring
      _ ≤ ‖r - t‖⁻¹ * (|bound a| * ‖r - t‖) +
          ‖r - t‖⁻¹ * (‖F' a‖ * ‖r - t‖) := by
        exact add_le_add (mul_le_mul_of_nonneg_left ha (nneg r)) le_rfl
      _ ≤ |bound a| + ‖F' a‖ := by
        simp only [← div_eq_inv_mul]
        apply_rules [add_le_add, div_le_of_le_mul₀] <;> first | rfl | positivity
  · exact bound_integrable.norm.add hF'_int.norm
  · apply h_diff.mono
    intro a ha
    suffices Tendsto
        (fun r => ‖r - t‖⁻¹ • (F r a - F t a - (r - t) • F' a))
        (𝓝[s] t) (𝓝 (0 : E)) by simpa
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq :
        (fun r => ‖r - t‖⁻¹ * ‖F r a - F t a - (r - t) • F' a‖) =
          fun r => ‖‖r - t‖⁻¹ • (F r a - F t a - (r - t) • F' a)‖ := by
      funext r
      rw [norm_smul_of_nonneg (nneg r)]
    rwa [hasDerivWithinAt_iff_tendsto, heq] at ha

end

end NSEMaxwell.DominatedWithin
