/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
ML017: source proof/body extraction.
SOURCE = AnalyticAt.eventually_analyticAt
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/ChangeOrigin.lean#L378
SOURCE_SHA256 = acda4eb054df857f353197ec8c9d8722c425fa0bd206198e9b04868dc3291663
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
  {x y : E} {r : ℝ≥0∞}

theorem _root_.GRTemp.ML017.endpoint (h : AnalyticAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, AnalyticAt 𝕜 f y :=
  (isOpen_analyticAt 𝕜 f).mem_nhds h

