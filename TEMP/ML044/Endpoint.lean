/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
ML044: isolated proof-body candidate.
Original: AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L238
Source SHA256: 23bb70a1bad8b88c338b504532e784a33bec653fe550442925672ff7e891b2f1
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Analytic.IsolatedZeros (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Filter Function Module Nat FormalMultilinearSeries EMetric Set
open scoped Topology
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f g : 𝕜 → E} {z₀ : 𝕜}
namespace AnalyticOnNhd
variable {U : Set 𝕜}

theorem _root_.GRTemp.ML044.endpoint (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U := by
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz

end AnalyticOnNhd
end
