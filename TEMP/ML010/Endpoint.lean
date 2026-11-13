/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic

/-!
ML010: source proof/body extraction.
SOURCE = AnalyticAt.congr
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/Basic.lean#L491
SOURCE_SHA256 = af3ee71ee027f74ea4bf2254978f841722b90b75dabd1452ec98ca65857d38ec
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
variable {f g : E → F} {s : Set E} {x : E}

theorem _root_.GRTemp.ML010.endpoint (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 g x :=
  let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt

