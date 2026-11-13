/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
ML029: isolated proof-body candidate.
Original: hasFDerivAt_tsum_of_isPreconnected
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/SmoothSeries.lean#L72
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

theorem _root_.GRTemp.ML029.endpoint (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n) (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    (hx : x ∈ s) : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  have A :
    ∀ x : E, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, f n x) atTop (𝓝 (∑' n, f n x)) := by
    intro y hy
    apply Summable.hasSum
    exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  refine hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hf')
    (fun t y hy => ?_) A hx
  exact HasFDerivAt.fun_sum fun n _ => hf n y hy

end
