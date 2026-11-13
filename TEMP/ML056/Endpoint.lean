/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
ML056 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/LinearAlgebra/Matrix/PosDef.lean#L245
Source SHA256: 09290b5923e167fcf959df64d00b039c7b99c4b236755728219bf5b5feaac24a
Source declaration: Matrix.PosDef.add_posSemidef
Source lines: 245–249
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Matrix
namespace Matrix
namespace PosDef
variable {m R : Type*} [Ring R] [PartialOrder R] [StarRing R]

theorem _root_.GRTemp.ML056.endpoint [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosSemidef) : (A + B).PosDef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hA.2 (x := x) hx) (hB.2 x)⟩

end PosDef
end Matrix
