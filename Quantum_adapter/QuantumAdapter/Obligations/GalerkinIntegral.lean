import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of parameter integrals on a closed time domain

The native NSSolution uses derivatives within the forward half-line. The
following dominated-convergence argument keeps that domain in the limiting
filter, so it also applies at time zero. No extension to negative time is used.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology

namespace QuantumAdapter.Obligations

noncomputable section

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A dominated derivative passes through a parameter integral within an arbitrary time set. -/
theorem hasFDerivWithinAt_integral_of_dominated_lip
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {μ : Measure α} {F : X → α → E} {F' : α → X →L[ℝ] E}
    {s : Set X} {t : X} (ht : t ∈ s)
    (hF : ∀ x ∈ s, Integrable (F x) μ) (hF' : Integrable F' μ)
    (bound : α → ℝ) (hbound : Integrable bound μ)
    (hbound_nonneg : ∀ a, 0 ≤ bound a)
    (hlip : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F x a - F t a‖ ≤ bound a * ‖x - t‖)
    (hderiv : ∀ᵐ a ∂μ, HasFDerivWithinAt (fun x => F x a) (F' a) s t) :
    HasFDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) s t := by
  have hinv (x : X) : 0 ≤ ‖x - t‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hidentity : ∀ᶠ x in 𝓝[s] t,
      ‖x - t‖⁻¹ * ‖((∫ a, F x a ∂μ) - ∫ a, F t a ∂μ) -
        (∫ a, F' a ∂μ) (x - t)‖ =
      ‖∫ a, ‖x - t‖⁻¹ • (F x a - F t a - F' a (x - t)) ∂μ‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [← norm_smul_of_nonneg (hinv x), integral_smul, integral_sub,
      integral_sub, ← ContinuousLinearMap.integral_apply hF']
    exacts [hF x hx, hF t ht, (hF x hx).sub (hF t ht),
      hF'.apply_continuousLinearMap _]
  rw [hasFDerivWithinAt_iff_tendsto, tendsto_congr' hidentity,
    ← tendsto_zero_iff_norm_tendsto_zero, ←
    show (∫ a : α, ‖t - t‖⁻¹ • (F t a - F t a - F' a (t - t)) ∂μ) = 0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun a => bound a + ‖F' a‖)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (((hF x hx).aestronglyMeasurable.sub (hF t ht).aestronglyMeasurable).sub
      (hF'.aestronglyMeasurable.apply_continuousLinearMap _)).const_smul _
  · filter_upwards [self_mem_nhdsWithin] with x hx
    apply hlip.mono
    intro a ha
    have ha_bound := ha x hx
    calc
      ‖‖x - t‖⁻¹ • (F x a - F t a - F' a (x - t))‖ =
          ‖‖x - t‖⁻¹ • (F x a - F t a) - ‖x - t‖⁻¹ • F' a (x - t)‖ := by
        rw [smul_sub]
      _ ≤ ‖‖x - t‖⁻¹ • (F x a - F t a)‖ +
          ‖‖x - t‖⁻¹ • F' a (x - t)‖ := norm_sub_le _ _
      _ = ‖x - t‖⁻¹ * ‖F x a - F t a‖ +
          ‖x - t‖⁻¹ * ‖F' a (x - t)‖ := by
        rw [norm_smul_of_nonneg (hinv x), norm_smul_of_nonneg (hinv x)]
      _ ≤ ‖x - t‖⁻¹ * (bound a * ‖x - t‖) +
          ‖x - t‖⁻¹ * (‖F' a‖ * ‖x - t‖) := by
        gcongr
        exact (F' a).le_opNorm _
      _ ≤ bound a + ‖F' a‖ := by
        simp only [← div_eq_inv_mul]
        apply add_le_add
        · apply div_le_of_le_mul₀ (norm_nonneg _) (hbound_nonneg a)
          exact le_rfl
        · apply div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _)
          exact le_rfl
  · exact hbound.add hF'.norm
  · apply hderiv.mono
    intro a ha
    suffices Tendsto (fun x => ‖x - t‖⁻¹ • (F x a - F t a - F' a (x - t)))
        (𝓝[s] t) (𝓝 0) by simpa
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun x => ‖x - t‖⁻¹ * ‖F x a - F t a - F' a (x - t)‖) =
        fun x => ‖‖x - t‖⁻¹ • (F x a - F t a - F' a (x - t))‖ := by
      funext x
      rw [norm_smul_of_nonneg (hinv x)]
    rwa [hasFDerivWithinAt_iff_tendsto, heq] at ha

/-- The same within-domain theorem in the scalar-time derivative convention. -/
theorem hasDerivWithinAt_integral_of_dominated_lip
    {μ : Measure α} {F : ℝ → α → E} {F' : α → E}
    {s : Set ℝ} {t : ℝ} (ht : t ∈ s)
    (hF : ∀ x ∈ s, Integrable (F x) μ) (hF' : Integrable F' μ)
    (bound : α → ℝ) (hbound : Integrable bound μ)
    (hbound_nonneg : ∀ a, 0 ≤ bound a)
    (hlip : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F x a - F t a‖ ≤ bound a * ‖x - t‖)
    (hderiv : ∀ᵐ a ∂μ, HasDerivWithinAt (fun x => F x a) (F' a) s t) :
    HasDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) s t := by
  let L : E →L[ℝ] ℝ →L[ℝ] E := ContinuousLinearMap.smulRightL ℝ ℝ E 1
  have hL : Integrable (fun a => L (F' a)) μ := L.integrable_comp hF'
  have hd : ∀ᵐ a ∂μ, HasFDerivWithinAt (fun x => F x a) (L (F' a)) s t :=
    hderiv.mono fun a ha => ha.hasFDerivWithinAt
  have h := hasFDerivWithinAt_integral_of_dominated_lip ht hF hL
    bound hbound hbound_nonneg hlip hd
  change HasFDerivWithinAt _ (L (∫ a, F' a ∂μ)) s t
  simpa only [ContinuousLinearMap.integral_comp_comm _ hF'] using h

end
end QuantumAdapter.Obligations
