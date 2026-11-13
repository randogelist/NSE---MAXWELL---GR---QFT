import QuantumAdapter.RegularityContracts
import SingularClosure.SobolevSmoothRealization
import Mathlib.Topology.Order.Compact

/-!
# Concrete Galerkin bounds and limit transfer

This module proves finite-horizon bounds for every fixed finite collection of
the actual full-mode Galerkin trajectories, including arbitrary mean.
It then supplies the tail-bound and limit-transfer steps used by the continuum
argument.

The continuum energy below is the actual weighted Fourier coefficient sum.
Its interpretation as a finite H3 norm requires the displayed summability
premise; a totalized infinite sum is not a Sobolev certificate.

No local PDE existence, nonlinear Galerkin convergence, or global
GalerkinAnalyticLaws inhabitant is asserted here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology

namespace QuantumAdapter.Assembly

open NSEMaxwell.Classical

noncomputable section

variable {ν : ℝ}

/-- All-order coefficient regularity gives native admissible spatial data.
The source's spatial lemmas allow an arbitrary mean; its separate mean-zero
global-existence target is not used. This theorem asserts no time evolution. -/
theorem allSobolev_nativeData (c : SingularClosure.FourierCoeff)
    (hc : ∀ s : ℕ, Memℓp (SingularClosure.sobolevWeightedCoeff s c) 2)
    (hsol : SingularClosure.SpectralSolenoidal c) :
    Data (SingularClosure.smoothFourierSynthesis c) := by
  have hr := SingularClosure.ALL_SOBOLEV_IMP_RAPID_SCALAR c hc
  refine ⟨SingularClosure.smoothFourierSynthesis_contDiff c hr, ?_, ?_⟩
  · exact SingularClosure.smoothFourierSynthesis_periodic c
  · intro x
    exact SingularClosure.smoothFourierSynthesis_divergence_free c hr hsol x

/-- The arbitrary-mean native spatial realization retains exactly the given
conjugate-symmetric coefficients. No PDE solution is inferred. -/
theorem allSobolev_nativeData_and_coefficients (c : SingularClosure.FourierCoeff)
    (hc : ∀ s : ℕ, Memℓp (SingularClosure.sobolevWeightedCoeff s c) 2)
    (hreal : SingularClosure.SpectralReality c)
    (hsol : SingularClosure.SpectralSolenoidal c) :
    Data (SingularClosure.smoothFourierSynthesis c) ∧
      SingularClosure.datumFourierCoeff (SingularClosure.smoothFourierSynthesis c) = c := by
  exact ⟨allSobolev_nativeData c hc hsol,
    SingularClosure.datumFourierCoeff_smoothFourierSynthesis c
      (SingularClosure.ALL_SOBOLEV_IMP_RAPID_SCALAR c hc) hreal⟩

/-- The actual finite H3 energy is continuous in its constrained phase. -/
theorem energy3_continuous (N : ℕ) : Continuous (energy3 N) := by
  unfold energy3
  apply continuous_finsetSum
  intro k hk
  apply continuous_finsetSum
  intro i hi
  have hterm : Continuous (fun q : Phase N =>
      h3Weight k * ‖phaseCoordinate N k i q‖ ^ 2) := by
    fun_prop
  simpa only [phaseCoordinate_apply, Complex.normSq_eq_norm_sq] using hterm

/-- Continuity is derived from the specified orbit derivative, not assumed. -/
theorem phaseFlow_orbit_continuous (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) : Continuous (fun t : ℝ => F.map N t q₀) := by
  exact continuous_iff_continuousAt.mpr
    (fun t => (F.orbit_derivative N q₀ t).continuousAt)

theorem centralEnergy_continuous (F : PhaseFlow ν) (N : ℕ)
    (a : Field) (ha : Data a) : Continuous (centralEnergy F N a ha) := by
  exact (energy3_continuous N).comp
    (phaseFlow_orbit_continuous F N (initialPhaseData N a ha))

/-- Every single actual Galerkin orbit is bounded on a closed finite horizon. -/
theorem centralEnergy_bounded_on_Icc (F : PhaseFlow ν) (N : ℕ)
    (a : Field) (ha : Data a) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T →
      centralEnergy F N a ha t ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).bddAbove_image
    (centralEnergy_continuous F N a ha).continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t ht hT
  exact (hC ⟨t, ⟨ht, hT⟩, rfl⟩).trans (le_max_right _ _)

/-- A finite collection of low cutoffs has one common actual energy bound. -/
theorem centralEnergy_finite_cutoffs_bounded (F : PhaseFlow ν)
    (a : Field) (ha : Data a) (T : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, N < K → ∀ t : ℝ,
      0 ≤ t → t ≤ T → centralEnergy F N a ha t ≤ C := by
  classical
  choose C hC₀ hC using
    (fun N : ℕ => centralEnergy_bounded_on_Icc F N a ha T)
  refine ⟨∑ N ∈ Finset.range K, C N,
    Finset.sum_nonneg (fun N hN => hC₀ N), ?_⟩
  intro N hN t ht hT
  exact (hC N t ht hT).trans
    (Finset.single_le_sum (fun n hn => hC₀ n) (Finset.mem_range.mpr hN))

/-- Only the high-cutoff tail needs a uniform analytic estimate. -/
theorem galerkinBoundAt_of_tail (F : PhaseFlow ν)
    (a : Field) (ha : Data a) (T : ℝ) (K : ℕ) (C : ℝ)
    (hTail : ∀ N : ℕ, K ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      centralEnergy F N a ha t ≤ C) :
    GalerkinBoundAt F a ha T := by
  obtain ⟨B, hB, hfinite⟩ := centralEnergy_finite_cutoffs_bounded F a ha T K
  refine ⟨max B C, hB.trans (le_max_left _ _), ?_⟩
  intro N hN t ht hT
  by_cases hNK : N < K
  · exact (hfinite N hNK t ht hT).trans (le_max_left _ _)
  · have hKN : K ≤ N := by omega
    exact (hTail N hKN t ht hT).trans (le_max_right _ _)

/-- The literal full Fourier H3 energy of a native physical field. -/
def continuumFourierEnergy (a : Field) : ℝ :=
  ∑' k : SingularClosure.Frequency, ∑ i : Fin 3,
    h3Weight k * Complex.normSq (SingularClosure.datumFourierCoeff a k i)

/-- The coefficient summability condition needed for a finite H3 interpretation. -/
def continuumFourierEnergySummable (a : Field) : Prop :=
  Summable (fun k : SingularClosure.Frequency => ∑ i : Fin 3,
    h3Weight k * Complex.normSq (SingularClosure.datumFourierCoeff a k i))

theorem continuumFourierEnergy_nonneg (a : Field) :
    0 ≤ continuumFourierEnergy a := by
  apply tsum_nonneg
  intro k
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (h3Weight_pos k).le (sq_nonneg _)

/-- One actual uniform energy approximation, at tolerance one, suffices for
the forward finite-horizon bound. The approximation remains a genuine
undischarged convergence premise. -/
theorem galerkinBoundAt_of_uniform_energy_approximation
    (F : PhaseFlow ν) (a : Field) (ha : Data a)
    (u : Velocity) (T : ℝ)
    (_hsummable : ∀ t ∈ Icc (0 : ℝ) T,
      continuumFourierEnergySummable (u t))
    (hcontinuous : ContinuousOn (fun t => continuumFourierEnergy (u t)) (Icc 0 T))
    (happrox : ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ t : ℝ,
      0 ≤ t → t ≤ T →
      |centralEnergy F N a ha t - continuumFourierEnergy (u t)| ≤ 1) :
    GalerkinBoundAt F a ha T := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcontinuous
  obtain ⟨K, hK⟩ := happrox
  apply galerkinBoundAt_of_tail F a ha T K (B + 1)
  intro N hN t ht hT
  have henergy : continuumFourierEnergy (u t) ≤ B :=
    hB ⟨t, ⟨ht, hT⟩, rfl⟩
  have herror := (abs_le.mp (hK N hN t ht hT)).2
  linarith

/-- Uniform convergence of actual scalar energies implies the tolerance-one
hypothesis used above. Neither convergence nor Sobolev regularity is assumed
under a global regularity name. -/
theorem galerkinBoundAt_of_uniform_energy_convergence
    (F : PhaseFlow ν) (a : Field) (ha : Data a)
    (u : Velocity) (T : ℝ)
    (hsummable : ∀ t ∈ Icc (0 : ℝ) T,
      continuumFourierEnergySummable (u t))
    (hcontinuous : ContinuousOn (fun t => continuumFourierEnergy (u t)) (Icc 0 T))
    (hconverges : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ N : ℕ, K ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
        |centralEnergy F N a ha t - continuumFourierEnergy (u t)| ≤ ε) :
    GalerkinBoundAt F a ha T := by
  exact galerkinBoundAt_of_uniform_energy_approximation F a ha u T
    hsummable hcontinuous (hconverges 1 (by norm_num))

/-- A cutoff-independent actual energy bound passes to its actual Fourier
energy limit. Summability records that the limit has the intended H3 meaning. -/
theorem continuumFourierEnergy_le_of_centralEnergy_tendsto
    (F : PhaseFlow ν) (a : Field) (ha : Data a)
    (u : Velocity) (t C : ℝ)
    (_hsummable : continuumFourierEnergySummable (u t))
    (hconverges : Tendsto (fun N : ℕ => centralEnergy F N a ha t)
      atTop (𝓝 (continuumFourierEnergy (u t))))
    (hbound : ∀ N : ℕ, 1 ≤ N → centralEnergy F N a ha t ≤ C) :
    continuumFourierEnergy (u t) ≤ C := by
  apply le_of_tendsto hconverges
  exact eventually_atTop.2 ⟨1, hbound⟩

/-- One fixed finite horizon provides the same limiting bound at every
strictly earlier time; the convergence premise is pointwise in time. -/
theorem continuumFourierEnergy_bounded_before
    (F : PhaseFlow ν) (a : Field) (ha : Data a)
    (u : Velocity) (T : ℝ) (hT : 0 < T)
    (hbounds : ∀ S : ℝ, 0 < S → GalerkinBoundAt F a ha S)
    (hsummable : ∀ t : ℝ, 0 ≤ t → t < T →
      continuumFourierEnergySummable (u t))
    (hconverges : ∀ t : ℝ, 0 ≤ t → t < T →
      Tendsto (fun N : ℕ => centralEnergy F N a ha t)
        atTop (𝓝 (continuumFourierEnergy (u t)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t < T →
      continuumFourierEnergy (u t) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hbounds (T + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro t ht htT
  apply continuumFourierEnergy_le_of_centralEnergy_tendsto F a ha u t C
    (hsummable t ht htT) (hconverges t ht htT)
  intro N hN
  exact hbound N hN t ht (by linarith)

/-- The actual Fourier-energy blowup alternative is incompatible with the
Galerkin bounds once the actual convergence premise has been proved.
No maximal PDE solution or smooth continuation is constructed here. -/
theorem no_finite_fourierEnergy_blowup
    (F : PhaseFlow ν) (a : Field) (ha : Data a)
    (u : Velocity) (T : ℝ) (hT : 0 < T)
    (hbounds : ∀ S : ℝ, 0 < S → GalerkinBoundAt F a ha S)
    (hsummable : ∀ t : ℝ, 0 ≤ t → t < T →
      continuumFourierEnergySummable (u t))
    (hconverges : ∀ t : ℝ, 0 ≤ t → t < T →
      Tendsto (fun N : ℕ => centralEnergy F N a ha t)
        atTop (𝓝 (continuumFourierEnergy (u t)))) :
    ¬ (∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
      C < continuumFourierEnergy (u t)) := by
  obtain ⟨C, hC, hbound⟩ :=
    continuumFourierEnergy_bounded_before F a ha u T hT hbounds hsummable hconverges
  intro hblowup
  obtain ⟨t, ht, htT, hlarge⟩ := hblowup C
  exact (not_lt_of_ge (hbound t ht htT)) hlarge

end

end QuantumAdapter.Assembly

