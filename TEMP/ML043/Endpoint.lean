/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Analytic.Uniqueness

/-!
ML043: isolated proof-body candidate.
Original: AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/Uniqueness.lean#L223
Source SHA256: 3c095cfff0c66f30905355dfe8918c74148cf462427b0b59f5322a495e002424
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Analytic.Uniqueness (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
open Set
open scoped Topology ENNReal NNReal
namespace AnalyticOnNhd

theorem _root_.GRTemp.ML043.endpoint {f g : E → F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) :
    EqOn f g U := by
  have hfg' : f - g =ᶠ[𝓝 z₀] 0 := hfg.mono fun z h => by simp [h]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀ hfg' hz

end AnalyticOnNhd
end
