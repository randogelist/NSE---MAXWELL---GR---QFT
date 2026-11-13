/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Geoffrey Irving, Stefan Kebekus
-/
import Mathlib.Analysis.Analytic.Constructions

/-!
ML036: isolated proof-body candidate.
Original: AnalyticAt.restrictScalars
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Analytic/Constructions.lean#L818
Source SHA256: 3bc1dd7547f45cee8ee3a341f0762deb56f42a155cce60757e14055b6f304964
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Analytic.Constructions (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open scoped Topology Ring
open Filter Asymptotics ENNReal NNReal
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {f : E → F} {x : E}

lemma _root_.GRTemp.ML036.endpoint (hf : AnalyticAt 𝕜' f x) :
    AnalyticAt 𝕜 f x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

end
