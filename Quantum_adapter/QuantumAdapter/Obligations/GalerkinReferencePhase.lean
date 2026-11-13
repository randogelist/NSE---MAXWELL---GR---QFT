import QuantumAdapter.Obligations.GalerkinReferenceEquation
import QuantumAdapter.Obligations.TraceProjection
import QuantumAdapter.Obligations.GalerkinWeightedPhase
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Native projected reference derivative and actual consistency residual

The reference curve differentiates as a curve in the constrained finite real
phase. Its consistency residual is an actual phase element, with literal
coefficients equal to the difference of projected finite and infinite
convections. Consequently the error-energy identity is an ordinary finite
Hilbert-space identity, including the one-sided initial derivative.
-/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (NSSolution Data SmoothVelocity)

noncomputable section

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

private def referencePhaseRetractionCLM (N : ℕ) : AmbientPhase N →L[ℝ] Phase N :=
  { toLinearMap := phaseRetraction N
    cont := (phaseRetraction N).continuous_of_finiteDimensional }

/-- Spectral constraints suffice to make an actual physical cutoff a native phase element. -/
theorem initialAmbient_mem_of_spectral (N : ℕ) (a : Field)
    (hsol : SpectralSolenoidal (datumFourierCoeff a)) :
    initialAmbient N a ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [initialAmbient_coeff, initialAmbient_coeff]
    by_cases hk : k ∈ fullModes N
    · rw [if_pos hk, if_pos (fullModes_neg_mem hk)]
      exact datumFourierCoeff_reality a k i
    · rw [if_neg hk, if_neg ((fullModes_neg_mem_iff N k).not.mpr hk)]
      simp
  · intro k
    simp_rw [initialAmbient_coeff]
    by_cases hk : k ∈ fullModes N
    · simp only [if_pos hk]
      exact hsol k
    · simp [hk]

/-- The actual projected time derivative is a constrained phase vector. -/
def referenceDerivativePhase (h : NSSolution ν a u p) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) : Phase N :=
  ⟨initialAmbient N (timeDerivative u t),
    initialAmbient_mem_of_spectral N _ (NSSolution.timeDerivative_fourier_solenoidal h t ht)⟩

@[simp]
theorem referenceDerivativePhase_coeff (h : NSSolution ν a u p) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    phaseCoeff (referenceDerivativePhase h N t ht) k i =
      if k ∈ fullModes N then datumFourierCoeff (timeDerivative u t) k i else 0 :=
  initialAmbient_coeff N (timeDerivative u t) k i

/-- Ambient finite Fourier differentiation follows from each literal integral coefficient. -/
theorem NSSolution.initialAmbient_hasDerivWithinAt (h : NSSolution ν a u p)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => initialAmbient N (u r))
      (initialAmbient N (timeDerivative u t)) (Ici 0) t := by
  have hc : HasDerivWithinAt
      (fun r => fun ki : PhaseIndex N => datumFourierCoeff (u r) ki.1.val ki.2)
      (fun ki : PhaseIndex N => datumFourierCoeff (timeDerivative u t) ki.1.val ki.2)
      (Ici 0) t :=
    hasDerivWithinAt_pi.mpr (fun ki => NSSolution.fourierCoeff_hasDerivWithinAt h t ht ki.1.val ki.2)
  have hto := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (fun ki : PhaseIndex N => datumFourierCoeff (u t) ki.1.val ki.2)).comp_hasDerivWithinAt t hc
  exact hto

/-- Differentiation of the projected reference in the actual finite constrained phase. -/
theorem referenceProjection_hasDerivWithinAt (h : NSSolution ν a u p)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (referenceProjection h N) (referenceDerivativePhase h N t ht) (Ici 0) t := by
  have hd := (referencePhaseRetractionCLM N).hasFDerivAt.comp_hasDerivWithinAt t
    (NSSolution.initialAmbient_hasDerivWithinAt h N t ht)
  have hr : referencePhaseRetractionCLM N (initialAmbient N (timeDerivative u t)) =
      referenceDerivativePhase h N t ht :=
    phaseRetraction_subtype N (referenceDerivativePhase h N t ht)
  rw [hr] at hd
  apply hd.congr_of_mem _ ht
  intro r hr
  rw [referenceProjection_eq h N r hr]
  change initialPhaseData N (u r) (NSSolution.spatial_data h r hr) =
    phaseRetraction N (initialPhaseData N (u r) (NSSolution.spatial_data h r hr)).val
  exact (phaseRetraction_subtype N _).symm

/-- The consistency residual is the projected actual derivative minus its finite drift. -/
def referenceResidualPhase (h : NSSolution ν a u p) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) : Phase N :=
  referenceDerivativePhase h N t ht - drift ν N (referenceProjection h N t)

/-- Exact consistency coefficients, with viscosity cancellation and arbitrary mean retained. -/
theorem referenceResidualPhase_coeff (h : NSSolution ν a u p) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    phaseCoeff (referenceResidualPhase h N t ht) k i =
      if k ∈ fullModes N then
        projectedTransportCoefficient k i (phaseSobolev 0 N (referenceProjection h N t))
          (phaseSobolev 0 N (referenceProjection h N t)) -
        projectedTransportCoefficient k i (referenceSobolevAt h 0 t ht)
          (referenceSobolevAt h 0 t ht)
      else 0 := by
  rw [referenceResidualPhase, phaseCoeff_sub]
  simp only [Pi.sub_apply]
  rw [referenceDerivativePhase_coeff,
    phaseCoeff_drift_eq_projectedTransport]
  by_cases hk : k ∈ fullModes N
  · rw [if_pos hk, if_pos hk, if_pos hk,
      referenceProjection_coeff h N t ht, if_pos hk,
      NSSolution.projected_fourier_equation h t ht k i]
    ring
  · simp [hk]

/-- The actual phase error has the reference-residual forced difference equation. -/
theorem referenceError_hasDerivWithinAt (F : PhaseFlow ν) (h : NSSolution ν a u p)
    (ha : Data a) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (referenceError F h ha N)
      (drift ν N (F.map N t (initialPhaseData N a ha)) -
        drift ν N (referenceProjection h N t) - referenceResidualPhase h N t ht) (Ici 0) t := by
  have hd := (F.orbit_derivative N (initialPhaseData N a ha) t).hasDerivWithinAt.sub
    (referenceProjection_hasDerivWithinAt h N t ht)
  have hr : drift ν N (F.map N t (initialPhaseData N a ha)) -
      drift ν N (referenceProjection h N t) - referenceResidualPhase h N t ht =
      drift ν N (F.map N t (initialPhaseData N a ha)) - referenceDerivativePhase h N t ht := by
    unfold referenceResidualPhase
    abel
  rw [hr]
  simpa only [referenceError, Pi.sub_apply] using! hd

/-- Exact Hs error-energy differentiation in the finite constrained Hilbert space. -/
theorem referenceError_sobolevEnergy_hasDerivWithinAt (F : PhaseFlow ν)
    (h : NSSolution ν a u p) (ha : Data a) (s N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => sobolevEnergy s N (referenceError F h ha N r))
      (2 * inner ℝ (sobolevWeightedPhaseCLM s N (referenceError F h ha N t))
        (sobolevWeightedPhaseCLM s N
          (drift ν N (F.map N t (initialPhaseData N a ha)) -
            drift ν N (referenceProjection h N t) - referenceResidualPhase h N t ht)))
      (Ici 0) t := by
  have hd := HasDerivWithinAt.norm_sq (F := Phase N)
    ((sobolevWeightedPhaseCLM s N).hasFDerivAt.comp_hasDerivWithinAt t
      (referenceError_hasDerivWithinAt F h ha N t ht))
  simpa only [Function.comp_def, sobolevWeightedPhase_norm_sq] using hd

end
end QuantumAdapter.Obligations
