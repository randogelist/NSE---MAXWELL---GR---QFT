/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/

import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
ML065 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/CStarAlgebra/Matrix.lean#L288
Source SHA256: 79518c9e51c4d0cf4083ab69a9ac7a2817305b48db1fe6f25ae1d678e12ce223
Source declaration: Matrix.instCStarRing
Source lines: 288–289
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
The exported structure is a named definition, not a registered global instance.
-/

set_option autoImplicit false
noncomputable section

open WithLp
open scoped Matrix Matrix.Norms.L2Operator
namespace Matrix
open LinearMap
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

def _root_.GRTemp.ML065.endpoint : CStarRing (Matrix n n 𝕜) where
  norm_mul_self_le M := le_of_eq <| Eq.symm <| l2_opNorm_conjTranspose_mul_self M

end Matrix
