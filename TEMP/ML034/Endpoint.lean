/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.SummableUniformlyOn

/-!
ML034: isolated proof-body candidate.
Original: SummableLocallyUniformlyOn.differentiableOn
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/SummableUniformlyOn.lean#L21
Source SHA256: 7eb8497cb24836cd6ef4f9dd0c312aa09659573db3cac1d87720828a3ebe4f4b
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Complex.SummableUniformlyOn (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section


lemma _root_.GRTemp.ML034.endpoint {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (h : SummableLocallyUniformlyOn f s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    DifferentiableOn ℂ (fun z ↦ ∑' n, f n z) s := by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha ↦ (hf2 a r hr).differentiableWithinAt

end
