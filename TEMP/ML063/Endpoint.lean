/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Lu-Ming Zhang
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
ML063 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean#L127
Source SHA256: 1ee785b6ebd213ad2ed971bf3c804afee8cc6ce52be69e63572b4cf1bdb5e880
Source declaration: Matrix.isUnit_iff_isUnit_det
Source lines: 127–128
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Matrix Equiv Equiv.Perm Finset
open scoped Ring
namespace Matrix
variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α)

theorem _root_.GRTemp.ML063.endpoint : IsUnit A ↔ IsUnit A.det := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]

end Matrix
