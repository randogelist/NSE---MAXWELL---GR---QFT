import QuantumAdapter.Dynamics

/-!
# Exact finite Fourier norm and initial-projection identities

The phase, coefficients and energies are the existing arbitrary-mean objects.
The weighted Euclidean linear map realizes the exact native H3 square root.
No uniform smooth-data summability or spatial Sobolev estimate is assumed here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter.Assembly

noncomputable section

open SingularClosure

theorem sum_fullModes_eq_sum_coordinates (N : ℕ) (f : Frequency → Fin 3 → ℝ) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3, f k i) =
      ∑ ki : PhaseIndex N, f ki.1.val ki.2 := by
  rw [Fintype.sum_prod_type, Finset.sum_coe_sort]

theorem phaseCoeff_mode (N : ℕ) (q : Phase N) (ki : PhaseIndex N) :
    phaseCoeff q ki.1.val ki.2 = q.val ki := by
  simp [phaseCoeff, extendCoeff, ki.1.property]

theorem energy0_eq_norm_sq (N : ℕ) (q : Phase N) :
    energy0 N q = ‖q‖ ^ 2 := by
  rw [energy0, sum_fullModes_eq_sum_coordinates]
  change _ = ‖q.val‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ki hki
  rw [phaseCoeff_mode, Complex.normSq_eq_norm_sq]

def weightedCoordinates (N : ℕ) : Phase N →ₗ[ℝ] AmbientPhase N where
  toFun q := WithLp.toLp 2 (fun ki : PhaseIndex N =>
    Real.sqrt (h3Weight ki.1.val) • q.val ki)
  map_add' := by
    intro q r
    ext ki
    exact smul_add (Real.sqrt (h3Weight ki.1.val)) (q.val ki) (r.val ki)
  map_smul' := by
    intro a q
    ext ki
    change Real.sqrt (h3Weight ki.1.val) • (a • q.val ki) =
      a • (Real.sqrt (h3Weight ki.1.val) • q.val ki)
    simp only [smul_smul]
    congr 1
    ring

@[simp]
theorem weightedCoordinates_apply (N : ℕ) (q : Phase N) (ki : PhaseIndex N) :
    weightedCoordinates N q ki = Real.sqrt (h3Weight ki.1.val) • q.val ki := rfl

theorem continuous_weightedCoordinates (N : ℕ) : Continuous (weightedCoordinates N) :=
  (weightedCoordinates N).continuous_of_finiteDimensional

theorem weightedCoordinates_norm_sq (N : ℕ) (q : Phase N) :
    ‖weightedCoordinates N q‖ ^ 2 = energy3 N q := by
  rw [EuclideanSpace.norm_sq_eq, energy3, sum_fullModes_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro ki hki
  rw [weightedCoordinates_apply, phaseCoeff_mode]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (h3Weight_pos ki.1.val).le, Complex.normSq_eq_norm_sq]

theorem sqrt_energy3_eq_norm (N : ℕ) (q : Phase N) :
    Real.sqrt (energy3 N q) = ‖weightedCoordinates N q‖ := by
  rw [← weightedCoordinates_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

theorem continuous_energy3 (N : ℕ) : Continuous (energy3 N) := by
  have h := (continuous_weightedCoordinates N).norm.pow 2
  simpa only [weightedCoordinates_norm_sq] using h

theorem continuous_sqrt_energy3 (N : ℕ) :
    Continuous (fun q : Phase N => Real.sqrt (energy3 N q)) := by
  simpa only [sqrt_energy3_eq_norm] using (continuous_weightedCoordinates N).norm

theorem sqrt_energy3_add_le (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N (q + r)) ≤
      Real.sqrt (energy3 N q) + Real.sqrt (energy3 N r) := by
  simp only [sqrt_energy3_eq_norm, map_add]
  exact norm_add_le _ _

theorem sqrt_energy3_sub_le (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N (q - r)) ≤
      Real.sqrt (energy3 N q) + Real.sqrt (energy3 N r) := by
  simp only [sqrt_energy3_eq_norm, map_sub]
  exact norm_sub_le _ _

theorem sqrt_energy3_le_add (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N q) ≤
      Real.sqrt (energy3 N (q - r)) + Real.sqrt (energy3 N r) := by
  simpa only [sub_add_cancel] using sqrt_energy3_add_le N (q - r) r

theorem abs_sqrt_energy3_sub_le (N : ℕ) (q r : Phase N) :
    |Real.sqrt (energy3 N q) - Real.sqrt (energy3 N r)| ≤
      Real.sqrt (energy3 N (q - r)) := by
  simp only [sqrt_energy3_eq_norm, map_sub]
  exact abs_norm_sub_norm_le _ _

def cutoffLambda (N : ℕ) : ℝ := 4 * Real.pi ^ 2 * (N : ℝ) ^ 2

def cutoffWeight (N : ℕ) : ℝ := (1 + cutoffLambda N) ^ 3

theorem cutoffLambda_nonneg (N : ℕ) : 0 ≤ cutoffLambda N := by
  unfold cutoffLambda
  positivity

theorem cutoffWeight_pos (N : ℕ) : 0 < cutoffWeight N := by
  have h := cutoffLambda_nonneg N
  unfold cutoffWeight
  positivity

theorem laplaceSymbol_le_cutoffLambda (N : ℕ) (k : Frequency)
    (hk : k ∈ fullModes N) : laplaceSymbol k ≤ cutoffLambda N := by
  rcases Finset.mem_insert.mp hk with hk | hk
  · subst k
    simpa [laplaceSymbol, galerkinFreqSq] using cutoffLambda_nonneg N
  · have hsq : galerkinFreqSq k ≤ (N : ℤ) ^ 2 :=
      ((mem_cutoffModes_iff N k).mp hk).2.2
    have hsqR : (galerkinFreqSq k : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hsq
    have h := mul_le_mul_of_nonneg_left hsqR (sq_nonneg (2 * Real.pi))
    simpa only [laplaceSymbol, cutoffLambda, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
      using h

theorem one_le_h3Weight (k : Frequency) : 1 ≤ h3Weight k := by
  have h := laplaceSymbol_nonneg k
  have hsq := sq_nonneg (laplaceSymbol k)
  have hcube := mul_nonneg h hsq
  unfold h3Weight
  nlinarith

theorem h3Weight_le_cutoffWeight (N : ℕ) (k : Frequency)
    (hk : k ∈ fullModes N) : h3Weight k ≤ cutoffWeight N := by
  have h := laplaceSymbol_le_cutoffLambda N k hk
  have hnonneg := laplaceSymbol_nonneg k
  unfold h3Weight cutoffWeight
  gcongr

theorem energy0_le_energy3 (N : ℕ) (q : Phase N) :
    energy0 N q ≤ energy3 N q := by
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  have hnorm : 0 ≤ Complex.normSq (phaseCoeff q k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_h3Weight k) hnorm

theorem energy3_le_cutoffWeight_mul_energy0 (N : ℕ) (q : Phase N) :
    energy3 N q ≤ cutoffWeight N * energy0 N q := by
  unfold energy3 energy0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hnorm : 0 ≤ Complex.normSq (phaseCoeff q k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  exact mul_le_mul_of_nonneg_right (h3Weight_le_cutoffWeight N k hk) hnorm

theorem dissipation_le_cutoffLambda_mul_energy0 (N : ℕ) (q : Phase N) :
    dissipation N q ≤ cutoffLambda N * energy0 N q := by
  unfold dissipation energy0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hnorm : 0 ≤ Complex.normSq (phaseCoeff q k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  exact mul_le_mul_of_nonneg_right (laplaceSymbol_le_cutoffLambda N k hk) hnorm

theorem cutoffSobolevFactor_sq (N : ℕ) :
    cutoffSobolevFactor N ^ 2 = cutoffWeight N := by
  unfold cutoffSobolevFactor cutoffWeight cutoffLambda
  rw [Real.sq_sqrt]
  positivity

theorem energy3_le_cutoffSobolevFactor_sq_mul_norm_sq (N : ℕ) (q : Phase N) :
    energy3 N q ≤ cutoffSobolevFactor N ^ 2 * ‖q‖ ^ 2 := by
  rw [cutoffSobolevFactor_sq, ← energy0_eq_norm_sq]
  exact energy3_le_cutoffWeight_mul_energy0 N q

theorem norm_le_sqrt_energy3 (N : ℕ) (q : Phase N) :
    ‖q‖ ≤ Real.sqrt (energy3 N q) := by
  have h := Real.sqrt_le_sqrt (energy0_le_energy3 N q)
  simpa only [energy0_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)] using h

theorem sqrt_energy3_le_cutoffSobolevFactor_mul_norm (N : ℕ) (q : Phase N) :
    Real.sqrt (energy3 N q) ≤ cutoffSobolevFactor N * ‖q‖ := by
  have h := Real.sqrt_le_sqrt (energy3_le_cutoffSobolevFactor_sq_mul_norm_sq N q)
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg (cutoffSobolevFactor_pos N).le
    (norm_nonneg q))] at h
  exact h

theorem fullModes_mono {N M : ℕ} (hNM : N ≤ M) : fullModes N ⊆ fullModes M := by
  intro k hk
  rcases Finset.mem_insert.mp hk with hk | hk
  · subst k
    exact zero_mem_fullModes M
  · apply Finset.mem_insert_of_mem
    rcases (mem_cutoffModes_iff N k).mp hk with ⟨hcoord, hne, hsq⟩
    apply (mem_cutoffModes_iff M k).mpr
    have hNMZ : (N : ℤ) ≤ (M : ℤ) := by exact_mod_cast hNM
    refine ⟨?_, hne, ?_⟩
    · intro i
      exact ⟨le_trans (neg_le_neg hNMZ) (hcoord i).1,
        le_trans (hcoord i).2 hNMZ⟩
    · have hN : (0 : ℤ) ≤ N := by exact_mod_cast Nat.zero_le N
      have hM : (0 : ℤ) ≤ M := by exact_mod_cast Nat.zero_le M
      nlinarith

def initialEnergyDensity (a : Field) (k : Frequency) : ℝ :=
  ∑ i : Fin 3, h3Weight k * Complex.normSq (datumFourierCoeff a k i)

theorem initialEnergyDensity_nonneg (a : Field) (k : Frequency) :
    0 ≤ initialEnergyDensity a k := by
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (h3Weight_pos k).le (sq_nonneg _)

theorem initialPhaseData_energy3_eq_sum (N : ℕ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    energy3 N (initialPhaseData N a ha) =
      ∑ k ∈ fullModes N, initialEnergyDensity a k := by
  unfold energy3 initialEnergyDensity
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  simp only [initialPhaseData, initialPhase_coeff, if_pos hk]

theorem initialPhaseData_energy3_mono {N M : ℕ} (hNM : N ≤ M)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    energy3 N (initialPhaseData N a ha) ≤ energy3 M (initialPhaseData M a ha) := by
  rw [initialPhaseData_energy3_eq_sum, initialPhaseData_energy3_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fullModes_mono hNM)
    (fun k hk hnot => initialEnergyDensity_nonneg a k)

end

end QuantumAdapter.Assembly
