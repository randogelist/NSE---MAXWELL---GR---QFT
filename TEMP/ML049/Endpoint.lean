/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
ML049: isolated proof-body candidate.
Original: tsum_neg
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L169
Source SHA256: f076038e732fb9432224fbac1f8ad6435cbc175b9211090a5e3b32081c96694f
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Topology.Algebra.InfiniteSum.Group (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: additive adaptation of the to_additive source generator.
-/

set_option autoImplicit false
noncomputable section

open Filter Finset Function
open scoped Topology
variable {α β : Type*} {L : SummationFilter β}
  [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]
  {f : β → α}

theorem _root_.GRTemp.ML049.endpoint : ∑'[L] b, -(f b) = -(∑'[L] b, f b) :=
  ((Homeomorph.neg α).isClosedEmbedding.map_tsum f (g := AddEquiv.neg α)).symm

end
