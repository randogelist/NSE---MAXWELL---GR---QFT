import QuantumAdapter.Obligations.GalerkinReferencePhase
import QuantumAdapter.Obligations.GalerkinReferenceBounds
import QuantumAdapter.Obligations.GalerkinErrorEnergy

/-!
# Native reference-error bootstrap and its exact remaining consistency input

The reference bound is derived from NSSolution itself. The error starts at zero
and satisfies its actual finite-dimensional derivative identity. A consistency
residual tending uniformly to zero therefore closes the requested Galerkin
bound. The residual convergence is an explicitly separate derived edge.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (NSSolution Data SmoothVelocity)

noncomputable section

/-- A forcing pairing costs one unit of energy and the squared forcing norm. -/
theorem sobolev_forcing_pairing_le (s N : ℕ) (e r : Phase N) :
    -(2 * inner ℝ (sobolevWeightedPhaseCLM s N e) (sobolevWeightedPhaseCLM s N r)) ≤
      sobolevEnergy s N e + sobolevEnergy s N r := by
  have h := sq_nonneg ‖sobolevWeightedPhaseCLM s N e + sobolevWeightedPhaseCLM s N r‖
  rw [norm_add_sq_real, sobolevWeightedPhase_norm_sq, sobolevWeightedPhase_norm_sq] at h
  linarith

/-- Actual finite-dimensional error dynamics with an arbitrary actual phase forcing. -/
theorem forced_reference_error_h3_rate_le (ν : ℝ) (hν : 0 < ν)
    (N : ℕ) (e v r : Phase N) (R : ℝ)
    (he : sobolevEnergy 3 N e ≤ 1) (hv : sobolevEnergy 3 N v ≤ R) :
    2 * inner ℝ (sobolevWeightedPhaseCLM 3 N e)
      (sobolevWeightedPhaseCLM 3 N (drift ν N (e + v) - drift ν N v - r)) ≤
      (referenceErrorGrowth ν R + 1) * sobolevEnergy 3 N e + sobolevEnergy 3 N r := by
  rw [map_sub, inner_sub_right]
  have hd := drift_reference_error_h3_rate_le ν hν N e v R he hv
  have hr := sobolev_forcing_pairing_le 3 N e r
  nlinarith

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- A globally defined rate function whose forward values are the actual error derivative. -/
def referenceErrorRate (F : PhaseFlow ν) (h : NSSolution ν a u p)
    (ha : Data a) (N : ℕ) (t : ℝ) : ℝ :=
  if ht : 0 ≤ t then
    2 * inner ℝ (sobolevWeightedPhaseCLM 3 N (referenceError F h ha N t))
      (sobolevWeightedPhaseCLM 3 N
        (drift ν N (F.map N t (initialPhaseData N a ha)) -
          drift ν N (referenceProjection h N t) - referenceResidualPhase h N t ht))
  else 0

theorem referenceErrorRate_hasDerivWithinAt (F : PhaseFlow ν)
    (h : NSSolution ν a u p) (ha : Data a) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => sobolevEnergy 3 N (referenceError F h ha N r))
      (referenceErrorRate F h ha N t) (Ici 0) t := by
  rw [referenceErrorRate, dif_pos ht]
  exact referenceError_sobolevEnergy_hasDerivWithinAt F h ha 3 N t ht

/-- The true native error rate obeys the stopped estimate with the literal consistency residual. -/
theorem referenceErrorRate_le (hν : 0 < ν) (F : PhaseFlow ν)
    (h : NSSolution ν a u p) (ha : Data a) (N : ℕ) (t R : ℝ) (ht : 0 ≤ t)
    (he : sobolevEnergy 3 N (referenceError F h ha N t) ≤ 1)
    (hv : sobolevEnergy 3 N (referenceProjection h N t) ≤ R) :
    referenceErrorRate F h ha N t ≤
      (referenceErrorGrowth ν R + 1) * sobolevEnergy 3 N (referenceError F h ha N t) +
        sobolevEnergy 3 N (referenceResidualPhase h N t ht) := by
  have heq : F.map N t (initialPhaseData N a ha) =
      referenceError F h ha N t + referenceProjection h N t := by
    unfold referenceError
    abel
  rw [referenceErrorRate, dif_pos ht, heq]
  exact forced_reference_error_h3_rate_le ν hν N _ _ _ R he hv

/-- All PDE and stopping hypotheses are discharged; only consistency convergence remains here. -/
theorem galerkinBoundAt_of_reference_residual_bound
    (hν : 0 < ν) (F : PhaseFlow ν) (h : NSSolution ν a u p) (ha : Data a)
    (T : ℝ) (hT : 0 < T) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hres : ∀ N : ℕ, ∀ t : ℝ, ∀ ht : 0 ≤ t, t ≤ T →
      sobolevEnergy 3 N (referenceResidualPhase h N t ht) ≤ δ N) :
    GalerkinBoundAt F a ha T := by
  obtain ⟨R, hR, href⟩ := NSSolution.exists_uniform_referenceProjection_sobolevEnergy h 3 T
  let E : ℕ → ℝ → ℝ := fun N t => sobolevEnergy 3 N (referenceError F h ha N t)
  let A : ℝ := referenceErrorGrowth ν R + 1
  have hA : 0 ≤ A := add_nonneg (referenceErrorGrowth_nonneg ν R hν hR) zero_le_one
  have hcont (N : ℕ) : ContinuousOn (E N) (Icc 0 T) := by
    apply ContinuousOn.mono (s := Ici (0 : ℝ)) _ Icc_subset_Ici_self
    intro t ht
    exact (referenceErrorRate_hasDerivWithinAt F h ha N t ht).continuousWithinAt
  have hder (N : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
      HasDerivWithinAt (E N) (referenceErrorRate F h ha N t) (Ici t) t :=
    (referenceErrorRate_hasDerivWithinAt F h ha N t ht.1).mono
      (Ici_subset_Ici.mpr ht.1)
  have hzero (N : ℕ) : E N 0 = 0 := referenceError_sobolevEnergy_initial F h ha 3 N
  have hestimate (N : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T)
      (he : E N t ≤ 1) : referenceErrorRate F h ha N t ≤ A * E N t + δ N := by
    change referenceErrorRate F h ha N t ≤
      (referenceErrorGrowth ν R + 1) * sobolevEnergy 3 N (referenceError F h ha N t) + δ N
    exact (referenceErrorRate_le hν F h ha N t R ht.1 he
      (href N t ht.1 ht.2.le)).trans
      (add_le_add le_rfl (hres N t ht.1 ht.2.le))
  obtain ⟨K, hK⟩ := stopped_energy_uniform_small E (referenceErrorRate F h ha)
    A T δ hA hcont hder hzero hestimate hδ 1 zero_lt_one
  apply galerkinBoundAt_of_reference_error_tail F h ha T K (Real.sqrt R) 1
    (Real.sqrt_nonneg _) zero_le_one
  · intro N hN t ht htT
    rw [Real.sq_sqrt hR]
    simpa only [sobolevEnergy_three] using href N t ht htT
  · intro N hN t ht htT
    simpa only [E, one_pow, sobolevEnergy_three] using hK N hN t ⟨ht, htT⟩

end
end QuantumAdapter.Obligations
