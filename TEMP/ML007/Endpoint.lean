/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Set.UnionLift

/-!
ML007: source proof/body extraction.
SOURCE = Set.iUnionLift_of_mem
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Data/Set/UnionLift.lean#L74
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
variable {S : ι → Set α} {f : ∀ i, S i → β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
variable {T : Set α} {hT : T ⊆ iUnion S}

theorem _root_.GRTemp.ML007.endpoint (x : T) {i : ι} (hx : (x : α) ∈ S i) :
    iUnionLift S f hf T hT x = f i ⟨x, hx⟩ := by obtain ⟨x, hx⟩ := x; exact hf _ _ _ _ _

end Set
