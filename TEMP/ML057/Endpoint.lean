/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
ML057 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/LinearAlgebra/Matrix/PosDef.lean#L507
Source SHA256: 09290b5923e167fcf959df64d00b039c7b99c4b236755728219bf5b5feaac24a
Source declaration: Matrix.PosDef.isUnit
Source lines: 507–512
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Matrix
namespace Matrix
namespace PosDef
variable {n K : Type*} [Fintype n] [Field K] [PartialOrder K] [StarRing K]

theorem _root_.GRTemp.ML057.endpoint [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : IsUnit M := by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : ∃ a ≠ 0, M *ᵥ a = 0 := by
    obtain ⟨a, b, ha⟩ := Function.not_injective_iff.mp <| mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, ha, mulVec_sub]⟩
  simpa [ha2] using hM.dotProduct_mulVec_pos ha

end PosDef
end Matrix
