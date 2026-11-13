import QuantumAdapter.Obligations.EnergyFourier
import QuantumAdapter.Obligations.EnergyBilinear

/-! Exact derivative phases and the native nonhomogeneous H3 energy expansion. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

def derivativeAmbient (N : ℕ) (j : Fin 3) (q : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => derivativeSymbol j ki.1.val * q.val ki)

theorem derivativeAmbient_coeff (N : ℕ) (j : Fin 3) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (derivativeAmbient N j q) k i =
      derivativeSymbol j k * phaseCoeff q k i := by
  by_cases hk : k ∈ fullModes N <;> simp [derivativeAmbient, extendCoeff, phaseCoeff, hk]

theorem derivativeAmbient_mem (N : ℕ) (j : Fin 3) (q : Phase N) :
    derivativeAmbient N j q ∈ phaseSubmodule N := by
  constructor
  · intro k i
    simpa only [derivativeAmbient_coeff, spectralMultiplier] using
      derivativeMultiplier_reality (phaseCoeff q) (phaseCoeff_reality q) j k i
  · intro k
    simp only [derivativeAmbient_coeff]
    calc
      _ = derivativeSymbol j k * ∑ i : Fin 3, (k i : ℂ) * phaseCoeff q k i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [phaseCoeff_solenoidal q k, mul_zero]

def phaseDerivative (N : ℕ) (j : Fin 3) (q : Phase N) : Phase N :=
  ⟨derivativeAmbient N j q, derivativeAmbient_mem N j q⟩

theorem phaseCoeff_phaseDerivative (N : ℕ) (j : Fin 3) (q : Phase N) :
    phaseCoeff (phaseDerivative N j q) = spectralMultiplier (derivativeSymbol j) (phaseCoeff q) := by
  funext k i
  exact derivativeAmbient_coeff N j q k i

theorem phaseDerivative_add (N : ℕ) (j : Fin 3) (q r : Phase N) :
    phaseDerivative N j (q + r) = phaseDerivative N j q + phaseDerivative N j r := by
  apply Subtype.ext
  ext ki
  change derivativeSymbol j ki.1.val * (q.val ki + r.val ki) =
    derivativeSymbol j ki.1.val * q.val ki + derivativeSymbol j ki.1.val * r.val ki
  ring

theorem phaseDerivative_smul (N : ℕ) (j : Fin 3) (s : ℝ) (q : Phase N) :
    phaseDerivative N j (s • q) = s • phaseDerivative N j q := by
  apply Subtype.ext
  ext ki
  change derivativeSymbol j ki.1.val * (s • q.val ki) =
    s • (derivativeSymbol j ki.1.val * q.val ki)
  exact mul_smul_comm _ _ _

def phaseDerivativeLinear (N : ℕ) (j : Fin 3) : Phase N →ₗ[ℝ] Phase N where
  toFun := phaseDerivative N j
  map_add' := phaseDerivative_add N j
  map_smul' := by intro s q; exact phaseDerivative_smul N j s q

def phaseDerivativeCLM (N : ℕ) (j : Fin 3) : Phase N →L[ℝ] Phase N :=
  { toLinearMap := phaseDerivativeLinear N j
    cont := (phaseDerivativeLinear N j).continuous_of_finiteDimensional }

@[simp] theorem phaseDerivativeCLM_apply (N : ℕ) (j : Fin 3) (q : Phase N) :
    phaseDerivativeCLM N j q = phaseDerivative N j q := rfl

theorem synthesis_phaseDerivative (N : ℕ) (j : Fin 3) (q : Phase N) :
    synthesis (phaseDerivative N j q) = coordinateDerivative (synthesis q) j := by
  change fullSynthesis N (phaseCoeff (phaseDerivative N j q)) =
    coordinateDerivative (fullSynthesis N (phaseCoeff q)) j
  rw [phaseCoeff_phaseDerivative, fullSynthesis_coordinateDerivative]

theorem phaseDerivative_commute (N : ℕ) (i j : Fin 3) (q : Phase N) :
    phaseDerivative N i (phaseDerivative N j q) =
      phaseDerivative N j (phaseDerivative N i q) := by
  apply Subtype.ext
  ext ki
  change derivativeSymbol i ki.1.val * (derivativeSymbol j ki.1.val * q.val ki) =
    derivativeSymbol j ki.1.val * (derivativeSymbol i ki.1.val * q.val ki)
  ring

def frequencyEnergy (m N : ℕ) (q : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, ∑ i : Fin 3,
    laplaceSymbol k ^ m * Complex.normSq (phaseCoeff q k i)

theorem frequencyEnergy_zero (N : ℕ) (q : Phase N) :
    frequencyEnergy 0 N q = ‖q‖ ^ 2 := by
  simpa only [frequencyEnergy, pow_zero, one_mul, energy0] using
    Assembly.energy0_eq_norm_sq N q

theorem frequencyEnergy_one (N : ℕ) (q : Phase N) :
    frequencyEnergy 1 N q = dissipation N q := by
  simp only [frequencyEnergy, pow_one, dissipation]

theorem frequencyEnergy_nonneg (m N : ℕ) (q : Phase N) :
    0 ≤ frequencyEnergy m N q := by
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (pow_nonneg (laplaceSymbol_nonneg k) m) (Complex.normSq_nonneg _)

theorem frequencyEnergy_derivative_sum (m N : ℕ) (q : Phase N) :
    (∑ j : Fin 3, frequencyEnergy m N (phaseDerivative N j q)) =
      frequencyEnergy (m + 1) N q := by
  unfold frequencyEnergy
  simp_rw [phaseCoeff_phaseDerivative, normSq_derivativeMultiplier]
  calc
    _ = ∑ k ∈ fullModes N, ∑ j : Fin 3, ∑ i : Fin 3,
        laplaceSymbol k ^ m *
          ((2 * Real.pi * (k j : ℝ)) ^ 2 * Complex.normSq (phaseCoeff q k i)) :=
      Finset.sum_comm
    _ = ∑ k ∈ fullModes N, ∑ i : Fin 3, ∑ j : Fin 3,
        laplaceSymbol k ^ m *
          ((2 * Real.pi * (k j : ℝ)) ^ 2 * Complex.normSq (phaseCoeff q k i)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      have hsum : (∑ j : Fin 3, (2 * Real.pi * (k j : ℝ)) ^ 2) = laplaceSymbol k :=
        sum_derivativeScale_sq k
      calc
        _ = (laplaceSymbol k ^ m * Complex.normSq (phaseCoeff q k i)) *
            ∑ j : Fin 3, (2 * Real.pi * (k j : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [hsum, pow_succ]; ring

theorem energy3_eq_frequencyEnergy (N : ℕ) (q : Phase N) :
    energy3 N q = frequencyEnergy 0 N q + 3 * frequencyEnergy 1 N q +
      3 * frequencyEnergy 2 N q + frequencyEnergy 3 N q := by
  have hpoint (k : Frequency) (i : Fin 3) :
      h3Weight k * Complex.normSq (phaseCoeff q k i) =
        laplaceSymbol k ^ 0 * Complex.normSq (phaseCoeff q k i) +
        3 * (laplaceSymbol k ^ 1 * Complex.normSq (phaseCoeff q k i)) +
        3 * (laplaceSymbol k ^ 2 * Complex.normSq (phaseCoeff q k i)) +
        laplaceSymbol k ^ 3 * Complex.normSq (phaseCoeff q k i) := by
    unfold h3Weight
    ring
  simp only [energy3, hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, frequencyEnergy]

theorem energy3_eq_derivative_norms (N : ℕ) (q : Phase N) :
    energy3 N q = ‖q‖^2 + 3 * (∑ i : Fin 3, ‖phaseDerivative N i q‖^2) +
      3 * (∑ i : Fin 3, ∑ j : Fin 3,
        ‖phaseDerivative N j (phaseDerivative N i q)‖^2) +
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ‖phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q))‖^2) := by
  simp_rw [← frequencyEnergy_zero N, frequencyEnergy_derivative_sum]
  exact energy3_eq_frequencyEnergy N q

end
end QuantumAdapter.Obligations
