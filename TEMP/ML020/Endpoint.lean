/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
ML020: source proof/body extraction.
SOURCE = ContDiffBump.one_of_mem_closedBall
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean#L137
SOURCE_SHA256 = b1abfd5f8861ac0fde77577d6fbe1207b2bdc8f4410b07764a2a781d2b63726b
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open Function Set Filter Metric
open scoped Topology Filter ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞}
namespace ContDiffBump

theorem _root_.GRTemp.ML020.endpoint (hx : x ∈ closedBall c f.rIn) : f x = 1 := by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx

end ContDiffBump
