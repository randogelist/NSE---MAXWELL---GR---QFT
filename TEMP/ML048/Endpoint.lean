/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
ML048: isolated proof-body candidate.
Original: Summable.mul_of_nonneg
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Normed/Ring/InfiniteSum.lean#L34
Source SHA256: d197a22a8073f6dfe1def4f755919629fdbbecdc4e72f82325eaff2759c4d62c
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Normed.Ring.InfiniteSum (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology
open Finset Filter
variable {ι ι' : Type*}

theorem _root_.GRTemp.ML048.endpoint {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g)
    (hf' : 0 ≤ f) (hg' : 0 ≤ g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (summable_prod_of_nonneg fun _ ↦ mul_nonneg (hf' _) (hg' _)).2 ⟨fun x ↦ hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩

end
