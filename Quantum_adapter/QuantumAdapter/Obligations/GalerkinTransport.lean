import QuantumAdapter.Obligations.GalerkinLimits
import QuantumAdapter.Assembly.Flow
import SingularClosure.FourierTransport

/-!
# Cutoff-independent fixed-frequency transport for the full native phase

The actual finite transport, including mean advection, is identified with the
existing continuous bilinear divergence convolution on H0. Its operator norm
bounds every fixed output coefficient independently of cutoff. These bounds
supply temporal equicontinuity in the continuum extraction.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly

noncomputable section

theorem fourierTensorCoefficient_phase_eq_sum (N : ℕ) (q r : Phase N)
    (k : Frequency) (j i : Fin 3) :
    fourierTensorCoefficient k j i (phaseSobolev 0 N q) (phaseSobolev 0 N r) =
      ∑ p ∈ fullModes N, phaseCoeff q p j * phaseCoeff r (k - p) i := by
  classical
  unfold fourierTensorCoefficient
  apply tsum_eq_sum
  intro p hp
  simp only [phaseSobolev_coeff, phaseCoeff_support q p hp j, zero_mul]

/-- The full arbitrary-mean finite transport equals the native untruncated H0 convolution. -/
theorem fullTransport_eq_divergenceTransport_phase (N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    fullTransport N (phaseCoeff q) k i =
      divergenceTransportCoefficient k i (phaseSobolev 0 N q) (phaseSobolev 0 N q) := by
  classical
  have hterm (p : Frequency) :
      (∑ j : Fin 3, phaseCoeff q p j * derivativeSymbol j (k - p)) =
        ∑ j : Fin 3, derivativeSymbol j k * phaseCoeff q p j := by
    simp_rw [derivativeSymbol_sub]
    calc
      _ = (∑ j : Fin 3, derivativeSymbol j k * phaseCoeff q p j) -
          (∑ j : Fin 3, derivativeSymbol j p * phaseCoeff q p j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [solenoidal_derivativeSymbol_sum _ (phaseCoeff_solenoidal q) p, sub_zero]
  rw [divergenceTransportCoefficient_apply]
  change (∑ p ∈ fullModes N,
    (∑ j : Fin 3, phaseCoeff q p j * derivativeSymbol j (k - p)) *
      phaseCoeff q (k - p) i) = _
  simp_rw [hterm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = derivativeSymbol j k *
        (∑ p ∈ fullModes N, phaseCoeff q p j * phaseCoeff q (k - p) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = _ := congrArg (fun z : ℂ => derivativeSymbol j k * z)
      (fourierTensorCoefficient_phase_eq_sum N q q k j i).symm

/-- A fixed projected transport coefficient as an actual bounded bilinear functional. -/
def projectedTransportCoefficient (k : Frequency) (i : Fin 3) :
    TorusSobolev 0 →L[ℂ] TorusSobolev 0 →L[ℂ] ℂ :=
  if k = 0 then divergenceTransportCoefficient k i else
    divergenceTransportCoefficient k i -
      ((k i : ℂ) / (∑ j : Fin 3, (k j : ℂ) ^ 2)) •
        ∑ j : Fin 3, (k j : ℂ) • divergenceTransportCoefficient k j

theorem projectedTransportCoefficient_apply (k : Frequency) (i : Fin 3)
    (c d : TorusSobolev 0) :
    projectedTransportCoefficient k i c d =
      coefficientLeray k (fun j => divergenceTransportCoefficient k j c d) i := by
  by_cases hk : k = 0
  · simp [projectedTransportCoefficient, coefficientLeray, hk]
  · simp only [projectedTransportCoefficient, coefficientLeray, hk, if_false,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, smul_eq_mul]
    ring

/-- The projected nonlinear coefficient has a cutoff-independent H0-square bound. -/
theorem projectedTransportCoefficient_norm_le_energy0 (N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    ‖projectedTransportCoefficient k i (phaseSobolev 0 N q) (phaseSobolev 0 N q)‖ ≤
      ‖projectedTransportCoefficient k i‖ * energy0 N q := by
  calc
    _ ≤ ‖projectedTransportCoefficient k i (phaseSobolev 0 N q)‖ *
        ‖phaseSobolev 0 N q‖ :=
      (projectedTransportCoefficient k i (phaseSobolev 0 N q)).le_opNorm _
    _ ≤ (‖projectedTransportCoefficient k i‖ * ‖phaseSobolev 0 N q‖) *
        ‖phaseSobolev 0 N q‖ :=
      mul_le_mul_of_nonneg_right
        ((projectedTransportCoefficient k i).le_opNorm _) (norm_nonneg _)
    _ = ‖projectedTransportCoefficient k i‖ * energy0 N q := by
      rw [mul_assoc, ← pow_two, phaseSobolev_norm_sq, sobolevEnergy_zero_order]

/-- Exact coefficient ODE in the common infinite-dimensional coefficient coordinates. -/
theorem phaseCoeff_drift_eq_projectedTransport (ν : ℝ) (N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    phaseCoeff (drift ν N q) k i =
      if k ∈ fullModes N then
        -((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff q k i -
          projectedTransportCoefficient k i (phaseSobolev 0 N q) (phaseSobolev 0 N q)
      else 0 := by
  change extendCoeff (drift ν N q).val k i = _
  rw [drift_eq_rawRhs, rawRhs_all_modes]
  congr 1
  rw [projectedTransportCoefficient_apply]
  congr 1
  funext j
  exact fullTransport_eq_divergenceTransport_phase N q k j

/-- Explicit fixed-output coefficient derivative bound; it is independent of N. -/
def coefficientDriftMajorant (ν C : ℝ) (k : Frequency) (i : Fin 3) : ℝ :=
  |ν| * laplaceSymbol k * Real.sqrt C + ‖projectedTransportCoefficient k i‖ * C

theorem coefficientDriftMajorant_nonneg (ν C : ℝ) (hC : 0 ≤ C)
    (k : Frequency) (i : Fin 3) : 0 ≤ coefficientDriftMajorant ν C k i := by
  unfold coefficientDriftMajorant
  exact add_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg _) (laplaceSymbol_nonneg _)) (Real.sqrt_nonneg _))
    (mul_nonneg (norm_nonneg _) hC)

theorem phaseCoeff_drift_norm_le (ν : ℝ) (N : ℕ) (q : Phase N)
    (C : ℝ) (hC : 0 ≤ C) (hbound : energy0 N q ≤ C)
    (k : Frequency) (i : Fin 3) :
    ‖phaseCoeff (drift ν N q) k i‖ ≤ coefficientDriftMajorant ν C k i := by
  rw [phaseCoeff_drift_eq_projectedTransport]
  split_ifs with hk
  · have hcoef : ‖phaseCoeff q k i‖ ≤ Real.sqrt C := by
      have h := weighted_coordinate_le_sqrt_sobolevEnergy 0 N q k i
      simp only [pow_zero, one_mul, sobolevEnergy_zero_order] at h
      exact h.trans (Real.sqrt_le_sqrt hbound)
    calc
      _ ≤ ‖-((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff q k i‖ +
          ‖projectedTransportCoefficient k i (phaseSobolev 0 N q) (phaseSobolev 0 N q)‖ :=
        norm_sub_le _ _
      _ ≤ (|ν| * laplaceSymbol k) * Real.sqrt C +
          ‖projectedTransportCoefficient k i‖ * C := by
        apply add_le_add
        · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_of_nonneg (laplaceSymbol_nonneg k)]
          exact mul_le_mul_of_nonneg_left hcoef
            (mul_nonneg (abs_nonneg _) (laplaceSymbol_nonneg _))
        · exact (projectedTransportCoefficient_norm_le_energy0 N q k i).trans
            (mul_le_mul_of_nonneg_left hbound (norm_nonneg _))
      _ = _ := rfl
  · simpa only [norm_zero] using coefficientDriftMajorant_nonneg ν C hC k i

/-- Actual phase-flow coefficient differentiation is in the common coordinates. -/
theorem phaseFlow_coefficient_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) (k : Frequency) (i : Fin 3) :
    HasDerivAt (fun s => phaseCoeff (F.map N s q) k i)
      (phaseCoeff (drift ν N (F.map N t q)) k i) t := by
  simpa only [Function.comp_def, phaseCoordinate_apply] using
    (phaseCoordinate N k i).hasFDerivAt.comp_hasDerivAt t (F.orbit_derivative N q t)

/-- The actual smooth datum supplies the same L2 bound for every cutoff and future time. -/
theorem central_energy0_le_majorant {ν : ℝ} (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    energy0 N (F.map N t (initialPhaseData N a ha)) ≤ initialSobolevMajorant 0 a := by
  have hdec := phaseFlow_energy0_antitone hν F N (initialPhaseData N a ha) ht
  rw [F.map_zero] at hdec
  exact hdec.trans (by simpa only [sobolevEnergy_zero_order] using
    initialPhaseData_sobolevEnergy_le_majorant 0 N a ha)

/-- Uniform time modulus for each literal Fourier coefficient on the entire forward half-line. -/
theorem central_coefficient_time_modulus {ν : ℝ} (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (k : Frequency) (i : Fin 3) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖phaseCoeff (F.map N t (initialPhaseData N a ha)) k i -
      phaseCoeff (F.map N s (initialPhaseData N a ha)) k i‖ ≤
      coefficientDriftMajorant ν (initialSobolevMajorant 0 a) k i * ‖t - s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Ici (0 : ℝ))
    (f' := fun r => phaseCoeff (drift ν N (F.map N r (initialPhaseData N a ha))) k i)
  · intro r hr
    exact (phaseFlow_coefficient_hasDerivAt F N (initialPhaseData N a ha) r k i).hasDerivWithinAt
  · intro r hr
    exact phaseCoeff_drift_norm_le ν N _ _ (initialSobolevMajorant_nonneg 0 a)
      (central_energy0_le_majorant hν F a ha N r hr) k i
  · exact convex_Ici 0
  · exact hs
  · exact ht

end
end QuantumAdapter.Obligations
