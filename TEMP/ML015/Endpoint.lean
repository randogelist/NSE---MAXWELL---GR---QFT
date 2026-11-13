/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Algebra.Ring.Periodic

/-!
ML015: source proof/body extraction.
SOURCE = Function.Periodic.zsmul
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Algebra/Ring/Periodic.lean#L155
SOURCE_SHA256 = 595ced3c0277252f889fa6f8c2f448c388e0a3f1dc83756fc29ab1290c2566b1
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

variable {α β : Type*} {f : α → β} {c c₁ c₂ : α}
open Set
namespace Function

theorem _root_.GRTemp.ML015.endpoint [AddGroup α] (h : Periodic f c) (n : ℤ) : Periodic f (n • c) := by
  rcases n with n | n
  · simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg

end Function
