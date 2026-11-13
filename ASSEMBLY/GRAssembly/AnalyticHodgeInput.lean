import GRAssembly.AnalyticHodgeSeries
import GRAdapter.UnitTorus
import Mathlib.Data.Nat.Choose.Bounds

/-! Uniform slab input bounds and fixed derivative-loss factorial absorption. -/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly

open Set Metric
open scoped BigOperators ContDiff

noncomputable section

theorem analyticHodge_factorial_shift_bound (n k : ℕ) :
    ((n + k).factorial : ℝ) ≤
      (2 : ℝ) ^ (n + k) * (n.factorial : ℝ) * (k.factorial : ℝ) := by
  have h : (n + k).factorial ≤ 2 ^ (n + k) * n.factorial * k.factorial := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial n k]
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.choose_le_two_pow (n + k) k))
  exact_mod_cast h

theorem analyticHodge_absorb_fixed_loss {C M A : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hA : 0 ≤ A) (n k : ℕ) :
    C * M * A ^ (n + k) * ((n + k).factorial : ℝ) ≤
      (C * M * A ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ k) *
        (2 * A) ^ n * (n.factorial : ℝ) := by
  calc
    _ ≤ C * M * A ^ (n + k) *
        ((2 : ℝ) ^ (n + k) * (n.factorial : ℝ) * (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (analyticHodge_factorial_shift_bound n k) (by positivity)
    _ = _ := by rw [pow_add, pow_add, mul_pow]; ring

theorem analyticHodge_order_monotone {A : ℝ} (hA : 1 ≤ A) (n k : ℕ) :
    A ^ n * (n.factorial : ℝ) ≤ A ^ (n + k) * ((n + k).factorial : ℝ) := by
  have hAp : A ^ n ≤ A ^ (n + k) := by
    rw [pow_add]
    exact le_mul_of_one_le_right (pow_nonneg (by linarith) n) (one_le_pow₀ hA)
  have hf : (n.factorial : ℝ) ≤ ((n + k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
  exact mul_le_mul hAp hf (by positivity) (by positivity)

theorem analyticHodge_open_slab_local_uniform_bound
    (f : Pressure) {I : Set ℝ} (hI : IsOpen I)
    (hf : AnalyticOnNhd ℝ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    {t : ℝ} (ht : t ∈ I) :
    ∃ r M A : ℝ, 0 < r ∧ 0 < M ∧ 1 ≤ A ∧ closedBall t r ⊆ I ∧
      ∀ (n : ℕ) (s : ℝ), s ∈ closedBall t r → ∀ x ∈ unitCube,
        ‖iteratedFDeriv ℝ n (fun z : ℝ × Vec => f z.1 z.2) (s, x)‖ ≤
          M * A ^ n * (n.factorial : ℝ) := by
  obtain ⟨R, hR, hRI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds ht)
  have hr : 0 < R / 2 := by positivity
  have hsub : closedBall t (R / 2) ⊆ I :=
    (closedBall_subset_ball (by linarith : R / 2 < R)).trans hRI
  have hK : IsCompact (closedBall t (R / 2) ×ˢ unitCube) :=
    isCompact_closedBall.prod NSEGR.isCompact_unitCube
  have ha : AnalyticOnNhd ℝ (fun z : ℝ × Vec => f z.1 z.2)
      (closedBall t (R / 2) ×ˢ unitCube) :=
    hf.mono (fun _ hz => hsub hz.1)
  obtain ⟨M, A, hM, hA, hb⟩ :=
    analyticOnNhd_compact_uniform_iteratedFDeriv_bound hK ha
  refine ⟨R / 2, M, max A 1, hr, hM, le_max_right _ _, hsub, ?_⟩
  intro n s hs x hx
  exact (hb n (s, x) ⟨hs, hx⟩).trans (by gcongr; exact le_max_left A 1)

end
end NSEGR.Assembly
