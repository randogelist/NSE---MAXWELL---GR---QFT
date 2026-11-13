/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic

/-!
ML018: source proof/body extraction.
SOURCE = mem_nhds_iff_exists_Ioo_subset
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Topology/Order/Basic.lean#L513
SOURCE_SHA256 = 3a847f1d21ae37df97ac9e7b1d9d6f36fa4db474e4d2dc5b692114882c4d3561
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open Set Filter TopologicalSpace Topology Function
universe u
variable {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

theorem _root_.GRTemp.ML018.endpoint [NoMaxOrder α] [NoMinOrder α] {a : α}
    {s : Set α} : s ∈ 𝓝 a ↔ ∃ l u, a ∈ Ioo l u ∧ Ioo l u ⊆ s :=
  mem_nhds_iff_exists_Ioo_subset' (exists_lt a) (exists_gt a)

