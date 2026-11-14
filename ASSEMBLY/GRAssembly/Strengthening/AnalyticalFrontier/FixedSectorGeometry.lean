import GRAssembly.Strengthening.AnalyticalFrontier.CheckpointQuantitative

/-!
Elementary complex-sector geometry used by the positive-time Wiener restart.
This module contains no NSE premise.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped Topology

namespace NSEGR.Strengthening
noncomputable section

/-- A fixed radial sector containing every positive real time below `T`. -/
def analyticalFixedSector (T : ℝ) : Set ℂ :=
  {z | 0 < ‖z‖ ∧ ‖z‖ < T ∧ ‖z‖ < 2 * z.re}

theorem analyticalFixedSector_re_pos {T : ℝ} {z : ℂ}
    (hz : z ∈ analyticalFixedSector T) : 0 < z.re := by
  rcases hz with ⟨hz0, _hzT, hzre⟩
  nlinarith

theorem analyticalFixedSector_real_mem {T h : ℝ}
    (hh : 0 < h) (hhT : h < T) :
    (h : ℂ) ∈ analyticalFixedSector T := by
  simp only [analyticalFixedSector, Set.mem_setOf_eq, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hh, Complex.ofReal_re]
  exact ⟨hh, hhT, by nlinarith⟩

theorem analyticalFixedSector_real_mul {T s : ℝ} {z : ℂ}
    (hz : z ∈ analyticalFixedSector T) (hs : 0 < s) (hs1 : s ≤ 1) :
    (s : ℂ) * z ∈ analyticalFixedSector T := by
  rcases hz with ⟨hz0, hzT, hzre⟩
  have hnorm : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [hnorm]
    exact mul_pos hs hz0
  · rw [hnorm]
    calc
      s * ‖z‖ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right hs1 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < T := hzT
  · have h := mul_lt_mul_of_pos_left hzre hs
    simpa [hnorm, Complex.mul_re, mul_assoc, mul_left_comm, mul_comm] using h

theorem analyticalFixedSector_norm_sq_lt {T : ℝ} {z : ℂ}
    (hz : z ∈ analyticalFixedSector T) :
    ‖z‖ ^ 2 < 2 * T * z.re := by
  rcases hz with ⟨hz0, hzT, hzre⟩
  have hT : 0 < T := hz0.trans hzT
  have h1 := mul_lt_mul_of_pos_left hzT hz0
  have h2 := mul_lt_mul_of_pos_left hzre hT
  nlinarith [h1, h2]

/-- Exact geometry package consumed by the fixed-sector analytic construction. -/
def ANALYTICAL_FIXED_SECTOR_GEOMETRY_CHECKPOINT : Prop :=
  ∀ T : ℝ, 0 < T →
    (∀ z : ℂ, z ∈ analyticalFixedSector T → 0 < z.re) ∧
    (∀ h : ℝ, 0 < h → h < T → (h : ℂ) ∈ analyticalFixedSector T) ∧
    (∀ (z : ℂ) (s : ℝ), z ∈ analyticalFixedSector T →
      0 < s → s ≤ 1 → (s : ℂ) * z ∈ analyticalFixedSector T) ∧
    (∀ z : ℂ, z ∈ analyticalFixedSector T → ‖z‖ ^ 2 < 2 * T * z.re)

theorem ANALYTICAL_FIXED_SECTOR_GEOMETRY_CHECKPOINT_NATIVE :
    ANALYTICAL_FIXED_SECTOR_GEOMETRY_CHECKPOINT := by
  intro T _hT
  exact ⟨
    fun _ hz => analyticalFixedSector_re_pos hz,
    fun _ hh hhT => analyticalFixedSector_real_mem hh hhT,
    fun _ _ hz hs hs1 => analyticalFixedSector_real_mul hz hs hs1,
    fun _ hz => analyticalFixedSector_norm_sq_lt hz⟩

end
end NSEGR.Strengthening
