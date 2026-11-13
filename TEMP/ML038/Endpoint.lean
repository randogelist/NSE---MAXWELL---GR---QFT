/-
Copyright (c) 2024 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich, Oliver Nash
-/
import Mathlib.Analysis.Complex.HasPrimitives

/-!
ML038: isolated proof-body candidate.
Original: DifferentiableOn.isExactOn_ball
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/HasPrimitives.lean#L290
Source SHA256: 6cf381a10ed0a913dd7bec999e88ab183d2579fc4445c4e795994e16e4be874f
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Complex.HasPrimitives (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Complex
variable {c : ℂ} {r : ℝ} {f : ℂ → E}
variable [CompleteSpace E]

theorem _root_.GRTemp.ML038.endpoint (hf : DifferentiableOn ℂ f (ball c r)) :
    IsExactOn f (ball c r) :=
  hf.isConservativeOn.isExactOn_ball hf.continuousOn

end Complex
end
