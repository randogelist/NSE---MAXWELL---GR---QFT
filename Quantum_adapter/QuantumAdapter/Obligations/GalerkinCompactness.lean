import QuantumAdapter.Obligations.GalerkinLimits
import Mathlib.Topology.Sequences

/-!
# Fixed-time compactness for actual full-mode Galerkin coefficients

The existing concrete compact Sobolev inclusion yields a convergent subsequence
of actual native phase coefficients under one uniform higher-order energy bound.
This is fixed-time spatial compactness, not yet the spacetime PDE endpoint.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology

namespace QuantumAdapter.Obligations

open SingularClosure

noncomputable section

/-- Evaluation of an actual unweighted coefficient in the concrete Sobolev space. -/
def sobolevCoefficientEvaluation (s : ℕ) (ki : FourierIndex) :
    TorusSobolev s →L[ℂ] ℂ :=
  (((torusSobolevWeight ki.1 : ℂ) ^ s)⁻¹) •
    ((lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 ki).comp
      (torusSobolevRepr s).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem sobolevCoefficientEvaluation_apply (s : ℕ) (ki : FourierIndex)
    (c : TorusSobolev s) : sobolevCoefficientEvaluation s ki c = c.val ki.1 ki.2 := by
  change ((torusSobolevWeight ki.1 : ℂ) ^ s)⁻¹ *
    ((torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2) = _
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero s (torusSobolevWeight_ne_zero _)), one_mul]

/-- Strong Sobolev convergence implies convergence of every literal Fourier coefficient. -/
theorem tendsto_coeff_of_tendsto_sobolev {ι : Type*} {l : Filter ι}
    (s : ℕ) (c : ι → TorusSobolev s) (d : TorusSobolev s)
    (h : Tendsto c l (𝓝 d)) (k : Frequency) (i : Fin 3) :
    Tendsto (fun n => (c n).val k i) l (𝓝 (d.val k i)) := by
  have he := ((sobolevCoefficientEvaluation s (k, i)).continuous.tendsto d).comp h
  simpa only [sobolevCoefficientEvaluation_apply, Function.comp_def] using he

/-- A squared actual Sobolev energy bound is exactly a closed-ball bound. -/
theorem phaseSobolev_mem_closedBall (s N : ℕ) (q : Phase N) (C : ℝ)
    (hC : 0 ≤ C) (hbound : sobolevEnergy s N q ≤ C) :
    phaseSobolev s N q ∈ Metric.closedBall (0 : TorusSobolev s) (Real.sqrt C) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := Real.sqrt_le_sqrt hbound
  rw [← phaseSobolev_norm_sq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- One extra uniform Sobolev order yields an actual convergent spatial subsequence. -/
theorem phase_sobolev_bounded_subsequence (s : ℕ) (K : ℕ → ℕ)
    (q : ∀ n : ℕ, Phase (K n)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, sobolevEnergy (s + 1) (K n) (q n) ≤ C) :
    ∃ (c : TorusSobolev s) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n : ℕ => torusSobolevInclusion s
        (phaseSobolev (s + 1) (K (φ n)) (q (φ n)))) atTop (𝓝 c) ∧
      (∀ k i, Tendsto (fun n : ℕ => phaseCoeff (q (φ n)) k i)
        atTop (𝓝 (c.val k i))) := by
  let S : Set (TorusSobolev s) := closure ((torusSobolevInclusion s) ''
    Metric.closedBall (0 : TorusSobolev (s + 1)) (Real.sqrt C))
  have hcompact : IsCompact S :=
    (torusSobolevInclusion_compact s).isCompact_closure_image_closedBall (Real.sqrt C)
  let f : ℕ → TorusSobolev s := fun n =>
    torusSobolevInclusion s (phaseSobolev (s + 1) (K n) (q n))
  have hf : ∀ n : ℕ, f n ∈ S := by
    intro n
    apply subset_closure
    exact ⟨phaseSobolev (s + 1) (K n) (q n),
      phaseSobolev_mem_closedBall (s + 1) (K n) (q n) C hC (hbound n), rfl⟩
  obtain ⟨c, hc, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hf
  refine ⟨c, φ, hφ, ?_, ?_⟩
  · simpa only [Function.comp_def, f] using hlim
  · intro k i
    have h := tendsto_coeff_of_tendsto_sobolev s (f ∘ φ) c hlim k i
    simpa only [Function.comp_def, f, torusSobolevInclusion_coeff, phaseSobolev_coeff] using h

/-- The fixed-time limit has the same reality and solenoidality as every native phase. -/
theorem phase_sobolev_bounded_real_solenoidal_subsequence (s : ℕ) (K : ℕ → ℕ)
    (q : ∀ n : ℕ, Phase (K n)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, sobolevEnergy (s + 1) (K n) (q n) ≤ C) :
    ∃ (c : TorusSobolev s) (φ : ℕ → ℕ), StrictMono φ ∧
      SpectralReality c.val ∧ SpectralSolenoidal c.val ∧
      (∀ k i, Tendsto (fun n : ℕ => phaseCoeff (q (φ n)) k i)
        atTop (𝓝 (c.val k i))) := by
  obtain ⟨c, φ, hφ, hnorm, hcoeff⟩ := phase_sobolev_bounded_subsequence s K q C hC hbound
  refine ⟨c, φ, hφ, ?_, ?_, hcoeff⟩
  · exact coefficient_limit_reality (K ∘ φ) (fun n => q (φ n)) c.val hcoeff
  · exact coefficient_limit_solenoidal (K ∘ φ) (fun n => q (φ n)) c.val hcoeff

end
end QuantumAdapter.Obligations
