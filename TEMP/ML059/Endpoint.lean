/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
ML059 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean#L239
Source SHA256: 5c87ec96e95be9c21e52857acc4892f9a6b7e69d7358f8d6fbbef93b0d249ef7
Source declaration: CFC.sqrt_nonneg
Source lines: 239–239
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open scoped NNReal
namespace CFC
variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

theorem _root_.GRTemp.ML059.endpoint (a : A) : 0 ≤ sqrt a := cfcₙ_predicate _ a

end CFC
