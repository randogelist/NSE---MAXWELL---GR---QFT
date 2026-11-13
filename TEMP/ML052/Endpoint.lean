/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
ML052 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L986
Source SHA256: 5d2f01069c6265873a372d4aed746c5d3411073b8acb108a180d02a84c832dca
Source declaration: AnalyticAt.contDiffAt
Source lines: 986–990
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Set Fin Filter Function
open scoped NNReal Topology ContDiff
universe u uE uF
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {x : E} {n : ℕ∞ω}

theorem _root_.GRTemp.ML052.endpoint [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ]
  rw [← analyticWithinAt_univ] at h
  exact h.contDiffWithinAt

