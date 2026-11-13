/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
ML022: source proof/body extraction.
SOURCE = derivWithin_of_mem_nhds
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L507
SOURCE_SHA256 = da1d29570f45bd14f5a37aa5b024d46b3076a47f04e9315bf72cd65f6505d55b
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology ENNReal NNReal
open Filter Asymptotics Set
universe u v
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

theorem _root_.GRTemp.ML022.endpoint (h : s ∈ 𝓝 x) : derivWithin f s x = deriv f x := by
  simp only [derivWithin, deriv, fderivWithin_of_mem_nhds h]

