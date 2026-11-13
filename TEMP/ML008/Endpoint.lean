/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Set.UnionLift

/-!
ML008: source proof/body extraction.
SOURCE = Set.liftCover
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Data/Set/UnionLift.lean#L155
SOURCE_SHA256 = 68789ff65258003813dda6ad16ff2723fa720a1bea0921fc069296f01b29bc02
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

variable {α : Type*} {ι β : Sort _}
namespace Set

noncomputable def _root_.GRTemp.ML008.endpoint (S : ι → Set α) (f : ∀ i, S i → β)
    (hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hS : iUnion S = univ) (a : α) : β :=
  iUnionLift S f hf univ hS.symm.subset ⟨a, trivial⟩

end Set
