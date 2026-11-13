import QuantumAdapter.Obligations.GalerkinSobolev
import QuantumAdapter.Assembly.Galerkin
import SingularClosure.PeriodicFourierInjective
import Mathlib.Topology.Sequences

/-!
# Coefficient limits of the actual full-mode Galerkin phases

Uniform finite Sobolev energies pass to genuinely square-summable coefficient
limits. Reality and solenoidality pass to those same limits. All-order bounds
therefore yield the existing actual smooth spatial realization. The pointwise
convergence premise is visible: a spacetime subsequence is not asserted here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology ContDiff ENNReal

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly

noncomputable section

/-- The actual finite product support, including all three mean coordinates. -/
def phaseFourierSupport (N : ℕ) : Finset FourierIndex :=
  (fullModes N).product Finset.univ

theorem weightedCoeff_eq_zero_of_not_mem_support (s N : ℕ) (q : Phase N)
    (ki : FourierIndex) (hki : ki ∉ phaseFourierSupport N) :
    sobolevWeightedCoeff s (phaseCoeff q) ki = 0 := by
  have hk : ki.1 ∉ fullModes N := by
    intro hk
    apply hki
    exact Finset.mem_product.mpr ⟨hk, Finset.mem_univ _⟩
  simp [sobolevWeightedCoeff, phaseCoeff_support q ki.1 hk ki.2]

theorem sum_phaseFourierSupport_eq_sobolevEnergy (s N : ℕ) (q : Phase N) :
    (∑ ki ∈ phaseFourierSupport N,
      ‖sobolevWeightedCoeff s (phaseCoeff q) ki‖ ^ 2) = sobolevEnergy s N q := by
  exact Finset.sum_product (fullModes N) Finset.univ
    (fun ki : FourierIndex => ‖sobolevWeightedCoeff s (phaseCoeff q) ki‖ ^ 2)

theorem finite_sum_weightedCoeff_sq_le_energy (s N : ℕ) (q : Phase N)
    (t : Finset FourierIndex) :
    (∑ ki ∈ t, ‖sobolevWeightedCoeff s (phaseCoeff q) ki‖ ^ 2) ≤
      sobolevEnergy s N q := by
  classical
  calc
    _ ≤ ∑ ki ∈ t ∪ phaseFourierSupport N,
        ‖sobolevWeightedCoeff s (phaseCoeff q) ki‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun ki hki hnot => sq_nonneg _)
    _ = ∑ ki ∈ phaseFourierSupport N,
        ‖sobolevWeightedCoeff s (phaseCoeff q) ki‖ ^ 2 := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro ki hki hnot
      rw [weightedCoeff_eq_zero_of_not_mem_support s N q ki hnot]
      simp
    _ = _ := sum_phaseFourierSupport_eq_sobolevEnergy s N q

/-- Every actual finite phase belongs to every native Fourier Sobolev space. -/
theorem phaseCoeff_mem_sobolev (s N : ℕ) (q : Phase N) :
    Memℓp (sobolevWeightedCoeff s (phaseCoeff q)) 2 := by
  apply memℓp_gen' (C := sobolevEnergy s N q)
  intro t
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    finite_sum_weightedCoeff_sq_le_energy s N q t

/-- The finite phase as an element of the existing concrete Hilbert Sobolev space. -/
def phaseSobolev (s N : ℕ) (q : Phase N) : TorusSobolev s :=
  ⟨phaseCoeff q, phaseCoeff_mem_sobolev s N q⟩

@[simp]
theorem phaseSobolev_coeff (s N : ℕ) (q : Phase N) :
    (phaseSobolev s N q).val = phaseCoeff q := rfl

theorem phaseSobolev_norm_sq (s N : ℕ) (q : Phase N) :
    ‖phaseSobolev s N q‖ ^ 2 = sobolevEnergy s N q := by
  rw [torusSobolev_norm_sq]
  simp only [phaseSobolev_coeff, ← sobolevWeightedCoeff_norm_eq]
  rw [tsum_eq_sum (s := phaseFourierSupport N)]
  · exact sum_phaseFourierSupport_eq_sobolevEnergy s N q
  · intro ki hki
    rw [weightedCoeff_eq_zero_of_not_mem_support s N q ki hki]
    simp

/-- A pointwise coefficient limit retains the full finite-energy bound in l². -/
theorem coefficient_limit_mem_sobolev (s : ℕ) (K : ℕ → ℕ)
    (q : ∀ n : ℕ, Phase (K n)) (c : FourierCoeff) (C : ℝ)
    (hbound : ∀ n : ℕ, sobolevEnergy s (K n) (q n) ≤ C)
    (hlim : ∀ k i, Tendsto (fun n : ℕ => phaseCoeff (q n) k i) atTop (𝓝 (c k i))) :
    Memℓp (sobolevWeightedCoeff s c) 2 := by
  apply memℓp_gen' (C := C)
  intro t
  have hfinite : Tendsto
      (fun n : ℕ => ∑ ki ∈ t, ‖sobolevWeightedCoeff s (phaseCoeff (q n)) ki‖ ^ 2)
      atTop (𝓝 (∑ ki ∈ t, ‖sobolevWeightedCoeff s c ki‖ ^ 2)) := by
    apply tendsto_finset_sum
    intro ki hki
    simpa only [sobolevWeightedCoeff] using
      (((hlim ki.1 ki.2).const_mul ((torusSobolevWeight ki.1 : ℂ) ^ s)).norm.pow 2)
  have hle : (∑ ki ∈ t, ‖sobolevWeightedCoeff s c ki‖ ^ 2) ≤ C := by
    apply le_of_tendsto hfinite
    exact Filter.Eventually.of_forall (fun n =>
      (finite_sum_weightedCoeff_sq_le_energy s (K n) (q n) t).trans (hbound n))
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hle

/-- Reality is closed under pointwise convergence of the actual coefficients. -/
theorem coefficient_limit_reality (K : ℕ → ℕ) (q : ∀ n : ℕ, Phase (K n))
    (c : FourierCoeff)
    (hlim : ∀ k i, Tendsto (fun n : ℕ => phaseCoeff (q n) k i) atTop (𝓝 (c k i))) :
    SpectralReality c := by
  intro k i
  have h := hlim (-k) i
  have heq : (fun n : ℕ => phaseCoeff (q n) (-k) i) =
      (fun n : ℕ => star (phaseCoeff (q n) k i)) := by
    funext n
    exact phaseCoeff_reality (q n) k i
  rw [heq] at h
  exact tendsto_nhds_unique h (hlim k i).star

/-- The finite solenoidal equations are closed under pointwise coefficient limits. -/
theorem coefficient_limit_solenoidal (K : ℕ → ℕ) (q : ∀ n : ℕ, Phase (K n))
    (c : FourierCoeff)
    (hlim : ∀ k i, Tendsto (fun n : ℕ => phaseCoeff (q n) k i) atTop (𝓝 (c k i))) :
    SpectralSolenoidal c := by
  intro k
  have h : Tendsto (fun n : ℕ => ∑ i : Fin 3, (k i : ℂ) * phaseCoeff (q n) k i)
      atTop (𝓝 (∑ i : Fin 3, (k i : ℂ) * c k i)) := by
    apply tendsto_finset_sum
    intro i hi
    exact (hlim k i).const_mul (k i : ℂ)
  have heq : (fun n : ℕ => ∑ i : Fin 3, (k i : ℂ) * phaseCoeff (q n) k i) =
      (fun _ : ℕ => (0 : ℂ)) := by
    funext n
    exact phaseCoeff_solenoidal (q n) k
  rw [heq] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- All-order actual phase bounds realize the limit as a native smooth datum. -/
theorem all_order_coefficient_limit_nativeData (K : ℕ → ℕ)
    (q : ∀ n : ℕ, Phase (K n)) (c : FourierCoeff)
    (hbound : ∀ s : ℕ, ∃ C : ℝ, ∀ n : ℕ, sobolevEnergy s (K n) (q n) ≤ C)
    (hlim : ∀ k i, Tendsto (fun n : ℕ => phaseCoeff (q n) k i) atTop (𝓝 (c k i))) :
    NSEMaxwell.Classical.Data (smoothFourierSynthesis c) ∧
      datumFourierCoeff (smoothFourierSynthesis c) = c := by
  have hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c) 2 := by
    intro s
    obtain ⟨C, hC⟩ := hbound s
    exact coefficient_limit_mem_sobolev s K q c C hC hlim
  exact allSobolev_nativeData_and_coefficients c hc
    (coefficient_limit_reality K q c hlim) (coefficient_limit_solenoidal K q c hlim)

/-- Coefficient agreement identifies the actual original periodic field. -/
theorem smoothFourierSynthesis_eq_original (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    smoothFourierSynthesis (datumFourierCoeff a) = a := by
  have hs : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s (datumFourierCoeff a)) 2 :=
    fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s a ha hp
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff a) hs
  apply datumFourierCoeff_injective_continuous_periodic _ _
    (smoothFourierSynthesis_contDiff _ hr).continuous ha.continuous
    (smoothFourierSynthesis_periodic _) hp
  exact datumFourierCoeff_smoothFourierSynthesis _ hr (datumFourierCoeff_reality a)

end
end QuantumAdapter.Obligations
