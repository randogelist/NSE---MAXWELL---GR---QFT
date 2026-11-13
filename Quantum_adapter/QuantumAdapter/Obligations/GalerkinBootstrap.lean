import QuantumAdapter.Obligations.GalerkinSobolev
import Mathlib.Analysis.ODE.Gronwall

/-!
# Stopped nonlinear error-energy bootstrap

The derivative inequality is required only while the actual nonnegative error
energy is at most one. A strict exponential fence proves that this condition
persists. Vanishing residuals therefore imply a uniform finite-horizon energy
error bound, without assuming in advance that the error stays small.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace QuantumAdapter.Obligations

noncomputable section

/-- Strict exponential fencing closes a stopped error-energy estimate. -/
theorem stopped_energy_exponential_bound
    (E E' : ℝ → ℝ) (A δ η T : ℝ)
    (hA : 0 ≤ A) (hη : 0 < η) (hδ : δ ≤ η / 2)
    (hsmall : η * Real.exp ((A + 1) * T) < 1)
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hzero : E 0 = 0)
    (hestimate : ∀ t ∈ Ico 0 T, E t ≤ 1 → E' t ≤ A * E t + δ) :
    ∀ t ∈ Icc 0 T, E t ≤ η * Real.exp ((A + 1) * t) := by
  let B : ℝ → ℝ := fun t => η * Real.exp ((A + 1) * t)
  have hK : 0 ≤ A + 1 := by linarith
  have hB (t : ℝ) : HasDerivAt B ((A + 1) * B t) t := by
    convert (((hasDerivAt_id t).const_mul (A + 1)).exp.const_mul η) using 1 <;>
      (try dsimp only [B]) <;> ring
  have hinit : E 0 ≤ B 0 := by simpa [B, hzero] using hη.le
  have hfence : ∀ t ∈ Ico (0 : ℝ) T, E t = B t → E' t < (A + 1) * B t := by
    intro t ht heq
    have hBT : B t ≤ η * Real.exp ((A + 1) * T) := by
      dsimp [B]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le hK)) hη.le
    have hE : E t ≤ 1 := heq.trans_le (hBT.trans hsmall.le)
    have hηB : η ≤ B t := by
      have hexp : 1 ≤ Real.exp ((A + 1) * t) :=
        Real.one_le_exp (mul_nonneg hK ht.1)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hη.le
    have hd := hestimate t ht hE
    rw [heq] at hd
    nlinarith
  exact fun t ht => image_le_of_deriv_right_lt_deriv_boundary hcont hderiv
    hinit hB hfence ht

/-- Residuals tending to zero force all stopped energy errors to zero uniformly. -/
theorem stopped_energy_uniform_small
    (E E' : ℕ → ℝ → ℝ) (A T : ℝ) (δ : ℕ → ℝ)
    (hA : 0 ≤ A)
    (hcont : ∀ N, ContinuousOn (E N) (Icc 0 T))
    (hderiv : ∀ N, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (E N) (E' N t) (Ici t) t)
    (hzero : ∀ N, E N 0 = 0)
    (hestimate : ∀ N, ∀ t ∈ Ico 0 T,
      E N t ≤ 1 → E' N t ≤ A * E N t + δ N)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      ∀ t ∈ Icc 0 T, E N t ≤ ε := by
  intro ε hε
  let R : ℝ := Real.exp ((A + 1) * T)
  have hR : 0 < R := Real.exp_pos _
  let η : ℝ := min ε 1 / (2 * R)
  have hmin : 0 < min ε 1 := lt_min hε zero_lt_one
  have hη : 0 < η := div_pos hmin (mul_pos (by norm_num) hR)
  have hηR : η * R = min ε 1 / 2 := by
    dsimp [η]
    field_simp [hR.ne'] <;> ring
  have hsmall : η * R < 1 := by
    rw [hηR]
    have h := min_le_right ε (1 : ℝ)
    linarith
  have htarget : η * R ≤ ε := by
    rw [hηR]
    have h := min_le_left ε (1 : ℝ)
    linarith
  have hev : ∀ᶠ N : ℕ in atTop, δ N < η / 2 :=
    hδ.eventually (gt_mem_nhds (half_pos hη))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨K, ?_⟩
  intro N hN t ht
  have hf := stopped_energy_exponential_bound (E N) (E' N) A (δ N) η T
    hA hη (hK N hN).le hsmall (hcont N) (hderiv N) (hzero N) (hestimate N)
  calc
    E N t ≤ η * Real.exp ((A + 1) * t) := hf t ht
    _ ≤ η * R := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))) hη.le
    _ ≤ ε := htarget

end
end QuantumAdapter.Obligations
