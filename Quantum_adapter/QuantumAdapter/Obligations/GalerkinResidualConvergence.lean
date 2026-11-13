import QuantumAdapter.Obligations.GalerkinHighTail
import QuantumAdapter.Obligations.GalerkinReferenceStability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform consistency convergence for an actual smooth reference

A coarse retained-frequency bound is combined with eight true Sobolev
derivatives of the reference. The resulting actual H3 residual is bounded by
C/N². The zero cutoff residual is exactly zero, so a single vanishing sequence
bounds every cutoff and every time in the finite interval.
-/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (NSSolution Data SmoothVelocity)

/-- The zero cutoff contains the mean and no other frequency. -/
theorem fullModes_zero_mem_iff (k : Frequency) : k ∈ fullModes 0 ↔ k = 0 := by
  constructor
  · intro hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · exact hk
    · have hc := (mem_cutoffModes_iff 0 k).mp hk
      have hzero : k = 0 := by
        funext i
        have hi := hc.1 i
        simpa only [Nat.cast_zero, neg_zero, Pi.zero_apply] using le_antisymm hi.2 hi.1
      exact False.elim (hc.2.1 hzero)
  · intro hk
    subst k
    exact zero_mem_fullModes 0

@[simp]
theorem projectedTransportCoefficient_zero_frequency (i : Fin 3) (c d : TorusSobolev 0) :
    projectedTransportCoefficient 0 i c d = 0 := by
  simp [projectedTransportCoefficient, divergenceTransportCoefficient, derivativeSymbol]

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- The mean-only Galerkin consistency residual vanishes exactly. -/
theorem referenceResidualPhase_zero_cutoff (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) : referenceResidualPhase h 0 t ht = 0 := by
  apply Subtype.ext
  apply extendCoeff_injective 0
  funext k i
  change phaseCoeff (referenceResidualPhase h 0 t ht) k i = phaseCoeff (0 : Phase 0) k i
  rw [referenceResidualPhase_coeff, phaseCoeff_zero]
  by_cases hk : k ∈ fullModes 0
  · have hk0 := (fullModes_zero_mem_iff k).mp hk
    subst k
    simp
  · simp [hk]

/-- Explicit consistency decay from the actual H0 and H8 norms. -/
theorem referenceResidual_h3_inverse_square_bound (h : NSSolution ν a u p)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) (C0 C8 : ℝ)
    (hC0 : 0 ≤ C0) (hC8 : 0 ≤ C8)
    (h0 : ‖referenceSobolevAt h 0 t ht‖ ^ 2 ≤ C0)
    (h8 : ‖referenceSobolevAt h 8 t ht‖ ^ 2 ≤ C8) :
    sobolevEnergy 3 N (referenceResidualPhase h N t ht) ≤
      (1728 * C0 * C8 * (1 + 4 * Real.pi ^ 2) ^ 7 * latticeSobolevConstant) *
        ((N : ℝ)⁻¹) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := latticeSobolevConstant_pos
  have htai := (reference_h0_tail_sq_le_h8 h N (by omega) t ht).trans
    (mul_le_mul_of_nonneg_left h8 (by positivity))
  have hfreq := retained_weight_tenth_sum_le N hN
  calc
    _ ≤ 1728 * ‖referenceSobolevAt h 0 t ht‖ ^ 2 *
        ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖ ^ 2 *
          ∑ k ∈ fullModes N, torusSobolevWeight k ^ 10 :=
      referenceResidual_h3_le_h0_tail h N t ht
    _ ≤ 1728 * C0 * (((N : ℝ)⁻¹) ^ 16 * C8) *
        ((1 + 4 * Real.pi ^ 2) ^ 7 * (N : ℝ) ^ 14 * latticeSobolevConstant) := by
      have hm : 1728 * ‖referenceSobolevAt h 0 t ht‖ ^ 2 *
          ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖ ^ 2 ≤
          1728 * C0 * (((N : ℝ)⁻¹) ^ 16 * C8) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h0 (by norm_num)) htai
          (sq_nonneg _) (mul_nonneg (by norm_num) hC0)
      exact mul_le_mul hm hfreq
        (Finset.sum_nonneg (fun k hk => pow_nonneg (torusSobolevWeight_pos k).le _))
        (mul_nonneg (mul_nonneg (by norm_num) hC0) (mul_nonneg (by positivity) hC8))
    _ = _ := by
      field_simp [hNr.ne']

/-- NSSolution itself supplies a vanishing sequence dominating every literal H3 residual. -/
theorem NSSolution.referenceResidual_vanishes_uniformly (h : NSSolution ν a u p) (T : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ N : ℕ, ∀ t : ℝ, ∀ ht : 0 ≤ t, t ≤ T →
        sobolevEnergy 3 N (referenceResidualPhase h N t ht) ≤ δ N := by
  obtain ⟨C0, hC0, hb0⟩ := NSSolution.exists_uniform_referenceSobolev_norm_sq h 0 T
  obtain ⟨C8, hC8, hb8⟩ := NSSolution.exists_uniform_referenceSobolev_norm_sq h 8 T
  let C : ℝ := 1728 * C0 * C8 * (1 + 4 * Real.pi ^ 2) ^ 7 * latticeSobolevConstant
  let δ : ℕ → ℝ := fun N => C * ((N : ℝ)⁻¹) ^ 2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using (hi.pow 2).const_mul C
  refine ⟨δ, hδ, ?_⟩
  intro N t ht htT
  by_cases hN : N = 0
  · subst N
    rw [referenceResidualPhase_zero_cutoff, sobolevEnergy_zero]
    simp only [δ, Nat.cast_zero, inv_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  · exact referenceResidual_h3_inverse_square_bound h N (by omega) t ht C0 C8
      hC0 hC8 (hb0 t ht htT) (hb8 t ht htT)

end
end QuantumAdapter.Obligations
