import QuantumAdapter.Assembly.Fourier
import SingularClosure.SobolevSmoothRealization

/-!
# Exact all-order Fourier Sobolev energies for the native Galerkin phases

The zero Fourier mode is retained. Every energy uses the actual native phase
coefficients and the vendored Methlib Sobolev weight. The smooth-data majorants
are constructed at every order, independently of the cutoff. This module does
not assert the nonlinear propagation or continuum compactness theorem.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly

noncomputable section

/-- One frequency's exact squared integral-order Sobolev coefficient norm. -/
def sobolevEnergyDensity (s : ℕ) (c : FourierCoeff) (k : Frequency) : ℝ :=
  ∑ i : Fin 3, ‖sobolevWeightedCoeff s c (k, i)‖ ^ 2

/-- The literal finite Sobolev energy, including the zero mode. -/
def sobolevEnergy (s N : ℕ) (q : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, sobolevEnergyDensity s (phaseCoeff q) k

theorem sobolevEnergyDensity_nonneg (s : ℕ) (c : FourierCoeff) (k : Frequency) :
    0 ≤ sobolevEnergyDensity s c k := by
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem sobolevEnergy_nonneg (s N : ℕ) (q : Phase N) :
    0 ≤ sobolevEnergy s N q := by
  exact Finset.sum_nonneg (fun k hk => sobolevEnergyDensity_nonneg s _ k)

@[simp]
theorem sobolevEnergy_zero (s N : ℕ) : sobolevEnergy s N 0 = 0 := by
  simp [sobolevEnergy, sobolevEnergyDensity, sobolevWeightedCoeff]

/-- This is equality with the native endpoint, not equivalence of norms. -/
@[simp]
theorem sobolevEnergy_three (N : ℕ) (q : Phase N) :
    sobolevEnergy 3 N q = energy3 N q := by
  unfold sobolevEnergy sobolevEnergyDensity energy3
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  exact (h3Coeff_eq_sobolevWeightedCoeff_sq _ k i).symm

@[simp]
theorem sobolevEnergy_zero_order (N : ℕ) (q : Phase N) :
    sobolevEnergy 0 N q = energy0 N q := by
  simp [sobolevEnergy, sobolevEnergyDensity, energy0, sobolevWeightedCoeff,
    Complex.normSq_eq_norm_sq]

theorem sobolevEnergyDensity_mono {s r : ℕ} (hsr : s ≤ r)
    (c : FourierCoeff) (k : Frequency) :
    sobolevEnergyDensity s c k ≤ sobolevEnergyDensity r c k := by
  apply Finset.sum_le_sum
  intro i hi
  rw [sobolevWeightedCoeff_norm_eq, sobolevWeightedCoeff_norm_eq]
  apply pow_le_pow_left₀ (mul_nonneg
    (pow_nonneg (torusSobolevWeight_pos k).le s) (norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (torusSobolevWeight_one_le k) hsr) (norm_nonneg _)

theorem sobolevEnergy_mono {s r : ℕ} (hsr : s ≤ r) (N : ℕ) (q : Phase N) :
    sobolevEnergy s N q ≤ sobolevEnergy r N q := by
  exact Finset.sum_le_sum (fun k hk => sobolevEnergyDensity_mono hsr _ k)

theorem energy3_le_sobolevEnergy {s : ℕ} (hs : 3 ≤ s) (N : ℕ) (q : Phase N) :
    energy3 N q ≤ sobolevEnergy s N q := by
  simpa only [sobolevEnergy_three] using sobolevEnergy_mono hs N q

/-- A weighted coordinate is controlled by the exact finite energy. -/
theorem weighted_coordinate_sq_le_sobolevEnergy (s N : ℕ) (q : Phase N)
    (k : Frequency) (hk : k ∈ fullModes N) (i : Fin 3) :
    ‖sobolevWeightedCoeff s (phaseCoeff q) (k, i)‖ ^ 2 ≤ sobolevEnergy s N q := by
  have hi : ‖sobolevWeightedCoeff s (phaseCoeff q) (k, i)‖ ^ 2 ≤
      sobolevEnergyDensity s (phaseCoeff q) k :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 3 => ‖sobolevWeightedCoeff s (phaseCoeff q) (k, j)‖ ^ 2)
      (fun j hj => sq_nonneg _) (Finset.mem_univ i)
  exact hi.trans (Finset.single_le_sum (s := fullModes N)
    (f := sobolevEnergyDensity s (phaseCoeff q))
    (fun l hl => sobolevEnergyDensity_nonneg s _ l) hk)

/-- Off-support coefficients are zero, so the same bound holds at every frequency. -/
theorem weighted_coordinate_sq_le_sobolevEnergy_all (s N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    ‖sobolevWeightedCoeff s (phaseCoeff q) (k, i)‖ ^ 2 ≤ sobolevEnergy s N q := by
  by_cases hk : k ∈ fullModes N
  · exact weighted_coordinate_sq_le_sobolevEnergy s N q k hk i
  · simpa [sobolevWeightedCoeff, phaseCoeff_support q k hk i] using
      sobolevEnergy_nonneg s N q

/-- A native energy bound gives a coefficient estimate with the actual Sobolev weight. -/
theorem weighted_coordinate_le_sqrt_sobolevEnergy (s N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    torusSobolevWeight k ^ s * ‖phaseCoeff q k i‖ ≤
      Real.sqrt (sobolevEnergy s N q) := by
  have h := Real.sqrt_le_sqrt (weighted_coordinate_sq_le_sobolevEnergy_all s N q k i)
  rw [Real.sqrt_sq (norm_nonneg _), sobolevWeightedCoeff_norm_eq] at h
  exact h

/-- An explicitly constructed all-order initial-data majorant. -/
def initialSobolevMajorant (s : ℕ) (a : Field) : ℝ :=
  3 * smoothDatumDecayConstant s a ^ 2 *
    ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4

theorem initialSobolevMajorant_nonneg (s : ℕ) (a : Field) :
    0 ≤ initialSobolevMajorant s a := by
  unfold initialSobolevMajorant
  positivity

@[simp]
theorem initialSobolevMajorant_three (a : Field) :
    initialSobolevMajorant 3 a = initialProjectionMajorant a := rfl

theorem initialSobolevEnergyDensity_le (s : ℕ) (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) :
    sobolevEnergyDensity s (datumFourierCoeff a) k ≤
      3 * smoothDatumDecayConstant s a ^ 2 * (torusSobolevWeight k)⁻¹ ^ 4 := by
  calc
    _ ≤ ∑ i : Fin 3, smoothDatumDecayConstant s a ^ 2 *
        (torusSobolevWeight k)⁻¹ ^ 4 :=
      Finset.sum_le_sum (fun i hi => smooth_datum_weightedCoeff_sq_le s a hs hp (k, i))
    _ = _ := by simp; ring

theorem initialPhaseData_sobolevEnergy_eq_sum (s N : ℕ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    sobolevEnergy s N (initialPhaseData N a ha) =
      ∑ k ∈ fullModes N, sobolevEnergyDensity s (datumFourierCoeff a) k := by
  unfold sobolevEnergy sobolevEnergyDensity
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  have hc := (initialPhase_coeff N a ha.smooth ha.periodic ha.divergence_free k i).trans
    (if_pos hk)
  simpa only [sobolevWeightedCoeff, initialPhaseData] using
    congrArg (fun z : ℂ => ‖(torusSobolevWeight k : ℂ) ^ s * z‖ ^ 2) hc

theorem initialPhaseData_sobolevEnergy_le_majorant (s N : ℕ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    sobolevEnergy s N (initialPhaseData N a ha) ≤ initialSobolevMajorant s a := by
  rw [initialPhaseData_sobolevEnergy_eq_sum]
  calc
    _ ≤ ∑ k ∈ fullModes N, 3 * smoothDatumDecayConstant s a ^ 2 *
        (torusSobolevWeight k)⁻¹ ^ 4 :=
      Finset.sum_le_sum (fun k hk => initialSobolevEnergyDensity_le s a ha.smooth ha.periodic k)
    _ = 3 * smoothDatumDecayConstant s a ^ 2 *
        ∑ k ∈ fullModes N, (torusSobolevWeight k)⁻¹ ^ 4 := by rw [Finset.mul_sum]
    _ ≤ initialSobolevMajorant s a := by
      apply mul_le_mul_of_nonneg_left
      · exact Summable.sum_le_tsum _ (fun k hk => by positivity)
          summable_torusSobolevWeight_inv_four
      · positivity

/-- Every integral Sobolev order has a cutoff-independent initial bound. -/
theorem initial_all_sobolev_bounds (a : NSEMaxwell.Classical.Field)
    (ha : NSEMaxwell.Classical.Data a) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, sobolevEnergy s N (initialPhaseData N a ha) ≤ C :=
  ⟨initialSobolevMajorant s a, initialSobolevMajorant_nonneg s a,
    fun N => initialPhaseData_sobolevEnergy_le_majorant s N a ha⟩

/-- True Sobolev membership implies summability of the literal energy density. -/
theorem sobolevEnergyDensity_summable (s : ℕ) (c : FourierCoeff)
    (hc : Memℓp (sobolevWeightedCoeff s c) 2) :
    Summable (sobolevEnergyDensity s c) := by
  exact summable_sum (fun i hi => sobolev_component_square_summable s c hc i)

theorem smooth_datum_sobolevEnergyDensity_summable (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    Summable (sobolevEnergyDensity s (datumFourierCoeff a)) :=
  sobolevEnergyDensity_summable s _ (SMOOTH_DATUM_MEM_TORUS_SOBOLEV s a ha hp)

/-- The finite initial energy is bounded by the actual convergent Fourier sum. -/
theorem initialPhaseData_sobolevEnergy_le_tsum (s N : ℕ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    sobolevEnergy s N (initialPhaseData N a ha) ≤
      ∑' k : Frequency, sobolevEnergyDensity s (datumFourierCoeff a) k := by
  rw [initialPhaseData_sobolevEnergy_eq_sum]
  exact Summable.sum_le_tsum _ (fun k hk => sobolevEnergyDensity_nonneg s _ k)
    (smooth_datum_sobolevEnergyDensity_summable s a ha.smooth ha.periodic)

end
end QuantumAdapter.Obligations
