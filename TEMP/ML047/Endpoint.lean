/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
ML047: isolated proof-body candidate.
Original: summable_int_iff_summable_nat_and_neg
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean#L508
Source SHA256: 008105deef888ea388644102337cf897571ef49acb594e25bf45b274916d58f8
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Topology.Algebra.InfiniteSum.NatInt (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: additive adaptation of the to_additive source generator.
-/

set_option autoImplicit false
noncomputable section

open Filter Finset Function Encodable
open scoped Topology
variable {G : Type*} [AddCommGroup G]
  [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]

lemma _root_.GRTemp.ML047.endpoint {f : ℤ → G} :
    Summable f ↔ (Summable fun n : ℕ ↦ f n) ∧ (Summable fun n : ℕ ↦ f (-n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Summable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

end
