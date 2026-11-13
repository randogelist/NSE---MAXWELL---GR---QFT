/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
ML028: isolated proof-body candidate.
Original: continuousOn_tsum
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Normed/Group/FunctionSeries.lean#L116
Source SHA256: 7852e142cb21d54b365d84ed4e1e2607a041242981cb96510b10f61b30aab5ac
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Normed.Group.FunctionSeries (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Set Metric TopologicalSpace Function Filter
open scoped Topology NNReal
variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem _root_.GRTemp.ML028.endpoint [TopologicalSpace β] {f : α → β → F} {s : Set β}
    (hf : ∀ i, ContinuousOn (f i) s) (hu : Summable u) (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    ContinuousOn (fun x => ∑' n, f n x) s := by
  refine (tendstoUniformlyOn_tsum hu hfu).continuousOn (Frequently.of_forall ?_)
  intro t
  exact continuousOn_finsetSum _ fun i _ => hf i

end
