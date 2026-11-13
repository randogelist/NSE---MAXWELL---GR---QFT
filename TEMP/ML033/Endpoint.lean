/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.Liouville

/-!
ML033: isolated proof-body candidate.
Original: Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Complex/Liouville.lean#L44
Source SHA256: 9f4bd4ef66951f410189d2f27f1de049d588411d9b0c174c8d7c5e56da18be31
Status: A_TIER_CANDIDATE; no local Lean execution.
Retained dependency: Mathlib.Analysis.Complex.Liouville (definitions and auxiliary declarations).
The original target theorem is not used as the replacement proof.
Extraction: literal target proof body, renamed export and explicit section context.
-/

set_option autoImplicit false
noncomputable section

open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory Bornology
open scoped Topology Filter NNReal Real
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Complex

theorem _root_.GRTemp.ML033.endpoint [CompleteSpace F] {c : ℂ} {R C : ℝ}
    {f : ℂ → F} (n : ℕ) (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  have hp (z) (hz : z ∈ sphere c R) : ‖(z - c)⁻¹ ^ (n + 1) • f z‖ ≤ C / (R ^ n * R) := by
    simpa [norm_smul, norm_pow, norm_inv, ← div_eq_inv_mul, mem_sphere_iff_norm.1 hz] using!
      (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
  have hq : iteratedDeriv n f c = n.factorial • (2 * π * I)⁻¹ •
    ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z := by
    have : (2 * π * I / n.factorial) ≠ 0 := by simp [Nat.factorial_ne_zero]
    rw [← inv_smul_smul₀ this (iteratedDeriv n f c), inv_div, div_eq_inv_mul, mul_comm,
      ← nsmul_eq_mul, smul_assoc]
    simp [← DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hR n hf]
  calc
    ‖iteratedDeriv n f c‖ = ‖n.factorial • (2 * π * I)⁻¹ •
      ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z‖ := by rw [hq]
    _ ≤ n.factorial * (R * (C / (R ^ (n + 1)))) := by
      rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, mul_le_mul_iff_right₀ (by positivity)]
      exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hp
    _ = n.factorial * C / R ^ n := by
      grind

end Complex
end
