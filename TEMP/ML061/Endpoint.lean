/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
ML061 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean#L722
Source SHA256: 5c87ec96e95be9c21e52857acc4892f9a6b7e69d7358f8d6fbbef93b0d249ef7
Source declaration: CFC.isUnit_sqrt_iff
Source lines: 722–724
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open scoped NNReal ContinuousFunctionalCalculus
open Ring
namespace CFC
variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

theorem _root_.GRTemp.ML061.endpoint (a : A) (ha : 0 ≤ a := by cfc_tac) : IsUnit (sqrt a) ↔ IsUnit a := by
  rw [sqrt_eq_rpow]
  exact isUnit_rpow_iff a _ (by simp) ha

end CFC
