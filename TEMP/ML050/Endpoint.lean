/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/

import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
ML050 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L653
Source SHA256: da1d29570f45bd14f5a37aa5b024d46b3076a47f04e9315bf72cd65f6505d55b
Source declaration: Filter.EventuallyEq.deriv
Source lines: 653–654
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology ENNReal NNReal
open Filter Asymptotics Set
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f f₁ : 𝕜 → F} {x : 𝕜}

theorem _root_.GRTemp.ML050.endpoint (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq

