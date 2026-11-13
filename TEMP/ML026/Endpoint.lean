/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic

/-!
ML026: isolated proof-body candidate.
Original: HasFPowerSeriesOnBall.analyticAt
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/Basic.lean#L139
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
variable {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞}

theorem _root_.GRTemp.ML026.endpoint (hf : HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.hasFPowerSeriesAt.analyticAt

end
