/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
ML051 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean#L263
Source SHA256: 9aba8c2c2b20b545331182e56325445f33f0a0851e9558e97595995e10045365
Source declaration: AnalyticAt.fderiv
Source lines: 263–266
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics Set
open scoped ENNReal Topology
universe u v
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {x : E}

theorem _root_.GRTemp.ML051.endpoint [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fderiv 𝕜 f) x := by
  rcases h with ⟨p, r, hp⟩
  exact hp.fderiv.analyticAt

