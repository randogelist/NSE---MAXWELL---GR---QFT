/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import Mathlib.Data.Set.Piecewise

/-!
ML014: source proof/body extraction.
SOURCE = Set.piecewise_eqOn
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Data/Set/Piecewise.lean#L67
SOURCE_SHA256 = cc1bd27199541d99cc175f5c214fa9e0a4ab78e6507ad121b55dac33840fa360
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

variable {α β : Type*}
open Equiv Equiv.Perm Function
namespace Set
variable (s : Set α) [∀ j, Decidable (j ∈ s)]

theorem _root_.GRTemp.ML014.endpoint (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _

end Set
