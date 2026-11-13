/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Analysis.Matrix.Order

/-!
ML058 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Matrix/Order.lean#L60
Source SHA256: fa8e30827d200098c48581a13b9147db22716074d68d7cdfe137a6c810661dd9
Source declaration: Matrix.nonneg_iff_posSemidef
Source lines: 60–60
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexOrder MatrixOrder
open Matrix
namespace Matrix
variable {𝕜 n : Type*} [RCLike 𝕜]

theorem _root_.GRTemp.ML058.endpoint {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

end Matrix
