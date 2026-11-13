/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
ML031: isolated proof-body candidate.
Original: hasFDerivAt_integral_of_dominated_of_fderiv_le
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ParametricIntegral.lean#L210
Source SHA256: 495f1a89774b147de1528e0213f519817d50fc3602724c9cbea633e9617c3375
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Calculus.ParametricIntegral (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open TopologicalSpace MeasureTheory Filter Metric
open scoped Topology Filter
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {F : H → α → E} {x₀ : H} {bound : α → ℝ} {s : Set H}

theorem _root_.GRTemp.ML031.endpoint {F' : H → α → H →L[𝕜] E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (F · a) (F' x a) x) :
    HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, ε_pos, hε⟩
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ (hε x₀_in)
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (F · a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x x_in ↦ (ha_deriv x (hε x_in)).hasFDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x (hε x_in)).trans (le_abs_self _)
  apply (hasFDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ ε_pos)
    hF_meas hF_int hF'_meas this bound_integrable diff_x₀).2

end
