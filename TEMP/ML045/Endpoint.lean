/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
ML045: isolated proof-body candidate.
Original: Real.summable_exp_nat_mul_iff
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/SpecialFunctions/Exp.lean#L460
Source SHA256: df9c7572f9816cccc1a7f8f6b03c2e11200654c18251fc7869c69ae63c20b9a6
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.SpecialFunctions.Exp (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open Asymptotics Bornology Finset Filter Function Metric Set Topology
open scoped Nat
namespace Real

lemma _root_.GRTemp.ML045.endpoint {a : ℝ} :
    Summable (fun n : ℕ ↦ exp (n * a)) ↔ a < 0 := by
  simp only [exp_nat_mul, summable_geometric_iff_norm_lt_one, norm_of_nonneg (exp_nonneg _),
    exp_lt_one_iff]

end Real
end
