/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
ML024: isolated proof-body candidate.
Original: FormalMultilinearSeries.le_radius_of_summable
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/ConvergenceRadius.lean#L133
Source SHA256: f6314e1932da1cf3b52545f51ed3c70ab5a5173850aa24d4601aa0d7f1bbfb60
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Analytic.ConvergenceRadius (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
namespace FormalMultilinearSeries
variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}

theorem _root_.GRTemp.ML024.endpoint (h : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm <| by
    simp only [← coe_nnnorm] at h
    exact mod_cast h

end FormalMultilinearSeries
end
