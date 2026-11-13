import QuantumAdapter.Obligations.GalerkinEnergyEstimates
import Mathlib.Analysis.Normed.Group.Tannery

/-! Actual fixed-frequency nonlinear limits from uniform Sobolev energies. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter
open scoped BigOperators Topology
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

def infiniteTensorProduct (c : FourierCoeff) (k : Frequency) (i j : Fin 3) : ℂ :=
  ∑' p : Frequency, c p j*c (k-p) i

def infiniteTransport (c : FourierCoeff) (k : Frequency) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k*infiniteTensorProduct c k i j

def nativeFourierRhs (ν : ℝ) (c : FourierCoeff) (k : Frequency) (i : Fin 3) : ℂ :=
  -((ν*laplaceSymbol k:ℝ):ℂ)*c k i-coefficientLeray k (infiniteTransport c k) i

theorem phase_coefficient_decay_of_energy (m N : ℕ) (q : Phase N) (C : ℝ)
    (hb : sobolevEnergy m N q ≤ C) (k : Frequency) (i : Fin 3) :
    ‖phaseCoeff q k i‖ ≤ Real.sqrt C*(torusSobolevWeight k)⁻¹^m := by
  have h := (weighted_coordinate_le_sqrt_sobolevEnergy m N q k i).trans
    (Real.sqrt_le_sqrt hb)
  have hd : ‖phaseCoeff q k i‖ ≤ Real.sqrt C/torusSobolevWeight k^m := by
    apply (le_div_iff₀ (pow_pos (torusSobolevWeight_pos k) m)).2
    simpa only [mul_comm] using h
  simpa only [div_eq_mul_inv,inv_pow] using hd

theorem fullTensorProduct_eq_tsum (N : ℕ) (q : Phase N) (k : Frequency) (i j : Fin 3) :
    fullTensorProduct N q q k i j = infiniteTensorProduct (phaseCoeff q) k i j := by
  symm
  unfold infiniteTensorProduct fullTensorProduct
  apply tsum_eq_sum
  intro p hp
  rw [phaseCoeff_support q p hp j,zero_mul]

/-- Only two actual uniform Sobolev bounds are needed for the fixed-frequency product limit. -/
theorem fullTensorProduct_tendsto (K : ℕ → ℕ) (q : ∀ n, Phase (K n))
    (c : FourierCoeff) (C0 C4 : ℝ)
    (h0 : ∀ n, sobolevEnergy 0 (K n) (q n) ≤ C0)
    (h4 : ∀ n, sobolevEnergy 4 (K n) (q n) ≤ C4)
    (hc : ∀ k i, Tendsto (fun n => phaseCoeff (q n) k i) atTop (𝓝 (c k i)))
    (k : Frequency) (i j : Fin 3) :
    Tendsto (fun n => fullTensorProduct (K n) (q n) (q n) k i j)
      atTop (𝓝 (infiniteTensorProduct c k i j)) := by
  have hsum : Summable (fun p : Frequency =>
      (Real.sqrt C4*Real.sqrt C0)*(torusSobolevWeight p)⁻¹^4) :=
    summable_torusSobolevWeight_inv_four.mul_left _
  have hb (n : ℕ) (p : Frequency) :
      ‖phaseCoeff (q n) p j*phaseCoeff (q n) (k-p) i‖ ≤
        (Real.sqrt C4*Real.sqrt C0)*(torusSobolevWeight p)⁻¹^4 := by
    have ha := phase_coefficient_decay_of_energy 4 (K n) (q n) C4 (h4 n) p j
    have hd := phase_coefficient_decay_of_energy 0 (K n) (q n) C0 (h0 n) (k-p) i
    simp only [pow_zero,mul_one] at hd
    rw [norm_mul]
    calc
      _ ≤ (Real.sqrt C4*(torusSobolevWeight p)⁻¹^4)*Real.sqrt C0 :=
        mul_le_mul ha hd (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
      _ = _ := by ring
  have h := tendsto_tsum_of_dominated_convergence hsum
    (fun p => (hc p j).mul (hc (k-p) i)) (Filter.Eventually.of_forall hb)
  change Tendsto (fun n => infiniteTensorProduct (phaseCoeff (q n)) k i j)
    atTop (𝓝 (infiniteTensorProduct c k i j)) at h
  simpa only [← fullTensorProduct_eq_tsum] using h

theorem fullTransport_tendsto (K : ℕ → ℕ) (q : ∀ n, Phase (K n))
    (c : FourierCoeff) (C0 C4 : ℝ)
    (h0 : ∀ n, sobolevEnergy 0 (K n) (q n) ≤ C0)
    (h4 : ∀ n, sobolevEnergy 4 (K n) (q n) ≤ C4)
    (hc : ∀ k i, Tendsto (fun n => phaseCoeff (q n) k i) atTop (𝓝 (c k i)))
    (k : Frequency) (i : Fin 3) :
    Tendsto (fun n => fullTransport (K n) (phaseCoeff (q n)) k i)
      atTop (𝓝 (infiniteTransport c k i)) := by
  simp only [← fullBilinearTransport_self,fullBilinearTransport_eq_tensor_divergence,
    infiniteTransport]
  apply tendsto_finset_sum
  intro j hj
  exact (fullTensorProduct_tendsto K q c C0 C4 h0 h4 hc k i j).const_mul _

theorem coefficientLeray_tendsto {v : ℕ → Fin 3 → ℂ} {w : Fin 3 → ℂ}
    (k : Frequency) (hv : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (w i))) (i : Fin 3) :
    Tendsto (fun n => coefficientLeray k (v n) i) atTop (𝓝 (coefficientLeray k w i)) := by
  by_cases hk : k=0
  · simp only [coefficientLeray,hk,if_true]
    exact hv i
  · simp only [coefficientLeray,hk,if_false]
    apply (hv i).sub
    apply Tendsto.div_const
    apply Tendsto.const_mul
    apply tendsto_finset_sum
    intro j hj
    exact (hv j).const_mul _

theorem phase_drift_coefficient_tendsto (ν : ℝ) (K : ℕ → ℕ)
    (q : ∀ n, Phase (K n)) (c : FourierCoeff) (C0 C4 : ℝ)
    (h0 : ∀ n, sobolevEnergy 0 (K n) (q n) ≤ C0)
    (h4 : ∀ n, sobolevEnergy 4 (K n) (q n) ≤ C4)
    (hc : ∀ k i, Tendsto (fun n => phaseCoeff (q n) k i) atTop (𝓝 (c k i)))
    (k : Frequency) (hk : ∀ᶠ n in atTop, k ∈ fullModes (K n)) (i : Fin 3) :
    Tendsto (fun n => phaseCoeff (drift ν (K n) (q n)) k i)
      atTop (𝓝 (nativeFourierRhs ν c k i)) := by
  have h := ((hc k i).const_mul (-((ν*laplaceSymbol k:ℝ):ℂ))).sub
    (coefficientLeray_tendsto k (fun j => fullTransport_tendsto K q c C0 C4 h0 h4 hc k j) i)
  apply h.congr'
  filter_upwards [hk] with n hn
  change -((ν*laplaceSymbol k:ℝ):ℂ)*phaseCoeff (q n) k i -
      coefficientLeray k (fullTransport (K n) (phaseCoeff (q n)) k) i =
    extendCoeff (drift ν (K n) (q n)).val k i
  rw [drift_eq_rawRhs,rawRhs_all_modes,if_pos hn]

theorem eventually_frequency_mem_fullModes (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : Frequency) :
    ∀ᶠ n in atTop, k ∈ fullModes (φ n+1) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (galerkinFreqSq k)
  apply Filter.eventually_atTop.mpr
  refine ⟨M+1,?_⟩
  intro n hn
  by_cases hk : k=0
  · subst k
    exact zero_mem_fullModes _
  · apply Finset.mem_insert_of_mem
    apply mem_cutoffModes_of_freqSq_le hk
    have hφn : n ≤ φ n := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))
    have hMN : M ≤ φ n+1 := by omega
    have hc : (M:ℤ) ≤ ((φ n+1:ℕ):ℤ) := by exact_mod_cast hMN
    have hz : (1:ℤ) ≤ ((φ n+1:ℕ):ℤ) := by exact_mod_cast (show 1≤φ n+1 by omega)
    nlinarith

end
end QuantumAdapter.Obligations
