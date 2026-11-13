/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
ML037: isolated proof-body candidate.
Original: AnalyticAt.re_ofReal
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean#L86
Source SHA256: 83fb8eba294cc5546aa3ff694213475d6779c30334a73809c788729460579a96
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.SpecialFunctions.Complex.Analytic (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Complex Set
open scoped Topology
variable {f : ℂ → ℂ} {x : ℝ}

lemma _root_.GRTemp.ML037.endpoint (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).re) x :=
  (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

end
