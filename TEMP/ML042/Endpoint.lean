/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Patrick Massot, Louis (Yiyang) Liu
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
ML042: isolated proof-body candidate.
Original: MeasureTheory.integral_tsum_of_summable_integral_norm
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean#L111
Source SHA256: 18b709ea5c9ef9136e3e75ded82a6135641e6e19688e0ca3abcb0af45648ab84
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.MeasureTheory.Integral.DominatedConvergence (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace ENNReal
open scoped Topology Interval
variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {m : MeasurableSpace α} {μ : Measure α}
namespace MeasureTheory

lemma _root_.GRTemp.ML042.endpoint {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ :=
  (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

end MeasureTheory
end
