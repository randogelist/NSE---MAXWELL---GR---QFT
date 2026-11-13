/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
ML013: source proof/body extraction.
SOURCE = Filter.EventuallyEq.fderiv
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/FDeriv/Congr.lean#L261
SOURCE_SHA256 = 5cad1d8c7480eac00c7004b6ec5ee9dd64ac80a833f10ad92936cdac4abe9673
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable {f f₁ : E → F} {x : E}

theorem _root_.GRTemp.ML013.endpoint (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq

