/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
ML030: isolated proof-body candidate.
Original: hasDerivAt_tsum_of_isPreconnected
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/SmoothSeries.lean#L89
Source SHA256: 5000d919737125bacacbc3df2f4e56284cd514dacc7f794c78f04d543ae47a78
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Calculus.SmoothSeries (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Set Metric TopologicalSpace Function Asymptotics Filter
open scoped Topology NNReal
variable {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [CompleteSpace F]
  [NormedSpace 𝕜 F] {u : α → ℝ}
variable {f : α → E → F} {f' : α → E → E →L[𝕜] F}
  {g : α → 𝕜 → F} {g' : α → 𝕜 → F}
  {s : Set E} {t : Set 𝕜} {x₀ x : E} {y₀ y : 𝕜}

theorem _root_.GRTemp.ML030.endpoint (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n) (hy₀ : y₀ ∈ t) (hg0 : Summable fun n => g n y₀)
    (hy : y ∈ t) : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg ⊢
  convert! hasFDerivAt_tsum_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  · exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1).map_tsum <|
      .of_norm_bounded hu fun n ↦ hg' n y hy
  · simpa

end
