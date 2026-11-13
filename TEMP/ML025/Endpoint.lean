/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic

/-!
ML025: isolated proof-body candidate.
Original: FormalMultilinearSeries.hasFPowerSeriesOnBall
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/Basic.lean#L1072
Source SHA256: af3ee71ee027f74ea4bf2254978f841722b90b75dabd1452ec98ca65857d38ec
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Analytic.Basic (definitions and auxiliary declarations).
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

theorem _root_.GRTemp.ML025.endpoint [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    HasFPowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }

end
