/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Geoffrey Irving, Stefan Kebekus
-/

import Mathlib.Analysis.Analytic.Constructions

/-!
ML054 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/Constructions.lean#L395
Source SHA256: 3bc1dd7547f45cee8ee3a341f0762deb56f42a155cce60757e14055b6f304964
Source declaration: AnalyticAt.curry_left
Source lines: 395–397
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology Ring
open Filter Asymptotics ENNReal NNReal
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem _root_.GRTemp.ML054.endpoint {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun x ↦ f (x, p.2)) p.1 :=
  AnalyticAt.comp₂ fa analyticAt_id analyticAt_const

