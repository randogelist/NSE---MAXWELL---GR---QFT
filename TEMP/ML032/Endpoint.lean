/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
ML032: isolated proof-body candidate.
Original: Complex.integral_boundary_rect_eq_zero_of_differentiableOn
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/CauchyIntegral.lean#L295
Source SHA256: 7a2022a8a02dbef3b5466edd2ba9e4123a898f1e0b0dc5dc320104832405f14b
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Complex.CauchyIntegral (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Complex

theorem _root_.GRTemp.ML032.endpoint (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn <|
    H.mono <|
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

end Complex
end
