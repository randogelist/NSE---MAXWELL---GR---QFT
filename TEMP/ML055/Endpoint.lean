/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
ML055 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/LinearAlgebra/Matrix/PosDef.lean#L441
Source SHA256: 09290b5923e167fcf959df64d00b039c7b99c4b236755728219bf5b5feaac24a
Source declaration: Matrix.PosDef.of_dotProduct_mulVec_pos
Source lines: 441–443
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Matrix
namespace Matrix
namespace PosDef
variable {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] [Fintype n]

theorem _root_.GRTemp.ML055.endpoint {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x)) : M.PosDef :=
  posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

end PosDef
end Matrix
