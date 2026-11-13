/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
ML021: source proof/body extraction.
SOURCE = ContDiffBump.tsupport_eq
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean#L157
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

theorem _root_.GRTemp.ML021.endpoint : tsupport f = closedBall c f.rOut := by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']

end ContDiffBump
