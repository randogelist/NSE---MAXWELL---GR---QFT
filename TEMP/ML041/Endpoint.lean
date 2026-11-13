/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
ML041: isolated proof-body candidate.
Original: intervalIntegral.integral_deriv_eq_sub
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L1176
Source SHA256: 5fd64054d9ae8bfce585ff809933a756bcf2d224ef144ae24c8fe8870c68050c
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Function Asymptotics
open scoped Topology ENNReal Interval NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace intervalIntegral
variable {a b : ℝ}
variable [CompleteSpace E] {f : ℝ → E}

theorem _root_.GRTemp.ML041.endpoint (hderiv : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hderiv x hx).hasDerivAt) hint

end intervalIntegral
end
