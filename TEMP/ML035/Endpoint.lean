/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
ML035: isolated proof-body candidate.
Original: DifferentiableOn.analyticAt
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/CauchyIntegral.lean#L625
Source SHA256: 7a2022a8a02dbef3b5466edd2ba9e4123a898f1e0b0dc5dc320104832405f14b
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Complex.CauchyIntegral (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Complex

theorem _root_.GRTemp.ML035.endpoint {s : Set ℂ} {f : ℂ → E} {z : ℂ}
    (hd : DifferentiableOn ℂ f s) (hz : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt

end Complex
end
