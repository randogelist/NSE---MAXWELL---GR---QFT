import QuantumAdapter.Obligations.NativeTimeTower
import QuantumAdapter.Obligations.FourierConvolutionLimits

/-! The actual coefficient limit has the prescribed initial trace and the native NSE evolution. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter
open scoped BigOperators Topology
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

theorem initialPhaseData_coefficient_tendsto (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (k : Frequency) (i : Fin 3) :
    Tendsto (fun j => phaseCoeff (initialPhaseData (φ j+1) a ha) k i)
      atTop (𝓝 (datumFourierCoeff a k i)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_frequency_mem_fullModes φ hφ k] with j hj
  simp only [initialPhaseData,initialPhase_coeff,if_pos hj]

/-- Every analytic input here is exactly the original P7 premise. -/
theorem native_continuum_tower_exists {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (h3 : ∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T) :
    ∃ d : ℕ → ℝ → FourierCoeff,
      FourierTimeTowerDerivative d ∧ FourierTimeTowerBounds d ∧
      (∀ n t, 0 ≤ t → SpectralReality (d n t) ∧ SpectralSolenoidal (d n t)) ∧
      d 0 0 = datumFourierCoeff a ∧
      ∀ t : ℝ, 0 ≤ t → d 1 t = nativeFourierRhs ν (d 0 t) := by
  obtain ⟨d,φ,hφ,hd,hb,hreal,hlim⟩ := native_time_tower_exists hν F a ha h3
  refine ⟨d,hd,hb,hreal,?_,?_⟩
  · funext k i
    have h := (hlim 0 k i 0).tendsto_at (show (0:ℝ)∈Icc (0:ℝ) (0:ℝ) by simp)
    simp only [phaseTimeJet_zero,F.map_zero] at h
    exact tendsto_nhds_unique h (initialPhaseData_coefficient_tendsto φ hφ a ha k i)
  · intro t ht
    let K : ℕ → ℕ := fun j => φ j+1
    let q : ∀ j, Phase (K j) := fun j => F.map (K j) t (initialPhaseData (K j) a ha)
    obtain ⟨C0,hC0,h0⟩ := galerkin_all_sobolev_bounds hν F a ha h3 0 (t+1) (by linarith)
    obtain ⟨C4,hC4,h4⟩ := galerkin_all_sobolev_bounds hν F a ha h3 4 (t+1) (by linarith)
    obtain ⟨H,hH⟩ := exists_nat_ge t
    have hcoeff (k : Frequency) (i : Fin 3) :
        Tendsto (fun j => phaseCoeff (q j) k i) atTop (𝓝 (d 0 t k i)) := by
      exact (hlim 0 k i H).tendsto_at ⟨ht,hH⟩
    funext k i
    have hR := phase_drift_coefficient_tendsto ν K q (d 0 t) C0 C4
      (fun j => h0 (K j) (by dsimp [K]; omega) t ht (by linarith))
      (fun j => h4 (K j) (by dsimp [K]; omega) t ht (by linarith))
      hcoeff k (eventually_frequency_mem_fullModes φ hφ k) i
    have hJ := (hlim 1 k i H).tendsto_at ⟨ht,hH⟩
    simp only [phaseTimeJet_one] at hJ
    exact tendsto_nhds_unique hJ hR

end
end QuantumAdapter.Obligations
