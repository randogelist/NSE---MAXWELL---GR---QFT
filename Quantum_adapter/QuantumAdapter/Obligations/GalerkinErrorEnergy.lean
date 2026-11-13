import QuantumAdapter.Obligations.GalerkinEnergyEstimates
import QuantumAdapter.Obligations.GalerkinWeightedPairing

/-!
# Stopped H3 stability of the actual finite Navier--Stokes drift

Three exact bilinear error terms are absorbed by viscosity. On the energy-one
stopping region the resulting coefficient depends only on viscosity and the
reference H3 bound, independently of the Galerkin cutoff.
-/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly

noncomputable section

/-- Exact native quadratic drift difference at reference plus error. -/
theorem drift_reference_error_expansion (ν : ℝ) (N : ℕ) (e v : Phase N) :
    drift ν N (e + v) - drift ν N v =
      bilinearConvection N e e + bilinearConvection N e v + bilinearConvection N v e -
        ν • phaseLaplacian N e := by
  rw [drift_eq_inviscid_sub_laplacian ν N (e + v), drift_eq_inviscid_sub_laplacian ν N v,
    ← bilinearConvection_self N (e + v), ← bilinearConvection_self N v,
    bilinearConvection_add_left, bilinearConvection_add_right,
    bilinearConvection_add_right, map_add, smul_add]
  abel

/-- Uniform mixed H3 pairing estimate in phase coordinates. -/
theorem weighted_bilinear_h3_rate_le (ν : ℝ) (hν : 0 < ν)
    (N : ℕ) (e q r : Phase N) :
    2 * inner ℝ (sobolevWeightedPhaseCLM 3 N e)
      (sobolevWeightedPhaseCLM 3 N (bilinearConvection N q r)) ≤
      (ν / 3) * sobolevEnergy 4 N e +
        (10368 * latticeSobolevConstant / ν) *
          (sobolevEnergy 3 N r * sobolevEnergy 3 N q +
            sobolevEnergy 3 N q * sobolevEnergy 3 N r) := by
  have h := weightedTransportPairing_young 3 N e q r (ν / 9) (by positivity)
  have hi := sobolevWeighted_inner_bilinearConvection 3 N e q r
  change inner ℝ (sobolevWeightedPhaseCLM 3 N e)
    (sobolevWeightedPhaseCLM 3 N (bilinearConvection N q r)) =
      -weightedTransportPairing 3 N e q r at hi
  have hcoef : 18 * ((2 : ℝ) ^ 3) ^ 2 * latticeSobolevConstant / (ν / 9) =
      10368 * latticeSobolevConstant / ν := by
    field_simp [hν.ne']
    ring
  have henergy : sobolevEnergy 2 N r * sobolevEnergy 3 N q +
      sobolevEnergy 2 N q * sobolevEnergy 3 N r ≤
        sobolevEnergy 3 N r * sobolevEnergy 3 N q +
          sobolevEnergy 3 N q * sobolevEnergy 3 N r :=
    add_le_add
      (mul_le_mul_of_nonneg_right (sobolevEnergy_mono (by omega : 2 ≤ 3) N r)
        (sobolevEnergy_nonneg 3 N q))
      (mul_le_mul_of_nonneg_right (sobolevEnergy_mono (by omega : 2 ≤ 3) N q)
        (sobolevEnergy_nonneg 3 N r))
  calc
    _ ≤ 2 * |weightedTransportPairing 3 N e q r| := by
      rw [hi]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by norm_num)
    _ ≤ _ := h
    _ ≤ _ := by
      rw [hcoef]
      have hfirst : 3 * (ν / 9) = ν / 3 := by ring
      rw [hfirst]
      have hK : 0 ≤ 10368 * latticeSobolevConstant / ν :=
        div_nonneg (mul_nonneg (by norm_num) latticeSobolevConstant_pos.le) hν.le
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left henergy hK)

/-- Coefficient for the stopped native reference-error estimate. -/
def referenceErrorGrowth (ν R : ℝ) : ℝ :=
  2 * ν + (10368 * latticeSobolevConstant / ν) * (2 + 4 * R)

theorem referenceErrorGrowth_nonneg (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) :
    0 ≤ referenceErrorGrowth ν R := by
  unfold referenceErrorGrowth
  have hL := latticeSobolevConstant_pos
  positivity

/-- On the stopping region E3(error)≤1, the native H3 difference rate is linear. -/
theorem drift_reference_error_h3_rate_le (ν : ℝ) (hν : 0 < ν)
    (N : ℕ) (e v : Phase N) (R : ℝ)
    (he : sobolevEnergy 3 N e ≤ 1) (hv : sobolevEnergy 3 N v ≤ R) :
    2 * inner ℝ (sobolevWeightedPhaseCLM 3 N e)
      (sobolevWeightedPhaseCLM 3 N (drift ν N (e + v) - drift ν N v)) ≤
        referenceErrorGrowth ν R * sobolevEnergy 3 N e := by
  let Q := sobolevEnergy 3 N e
  let V := sobolevEnergy 3 N v
  let D := sobolevEnergy 4 N e
  let K := 10368 * latticeSobolevConstant / ν
  have hQ : 0 ≤ Q := sobolevEnergy_nonneg 3 N e
  have hV : 0 ≤ V := sobolevEnergy_nonneg 3 N v
  have hD : 0 ≤ D := sobolevEnergy_nonneg 4 N e
  have hK : 0 ≤ K :=
    div_nonneg (mul_nonneg (by norm_num) latticeSobolevConstant_pos.le) hν.le
  change Q ≤ 1 at he
  have hQ2 : Q * Q ≤ Q := by nlinarith
  have hVQ : V * Q ≤ R * Q := mul_le_mul_of_nonneg_right hv hQ
  have hself := weighted_bilinear_h3_rate_le ν hν N e e e
  have hleft := weighted_bilinear_h3_rate_le ν hν N e e v
  have hright := weighted_bilinear_h3_rate_le ν hν N e v e
  have hsum :
      2 * inner ℝ (sobolevWeightedPhaseCLM 3 N e)
        (sobolevWeightedPhaseCLM 3 N (bilinearConvection N e e)) +
      2 * inner ℝ (sobolevWeightedPhaseCLM 3 N e)
        (sobolevWeightedPhaseCLM 3 N (bilinearConvection N e v)) +
      2 * inner ℝ (sobolevWeightedPhaseCLM 3 N e)
        (sobolevWeightedPhaseCLM 3 N (bilinearConvection N v e)) ≤
      ν * D + K * (2 + 4 * R) * Q := by
    have hKK := mul_le_mul_of_nonneg_left hQ2 hK
    have hKV := mul_le_mul_of_nonneg_left hVQ hK
    change _ ≤ (ν / 3) * D + K * (Q * Q + Q * Q) at hself
    change _ ≤ (ν / 3) * D + K * (V * Q + Q * V) at hleft
    change _ ≤ (ν / 3) * D + K * (Q * V + V * Q) at hright
    nlinarith
  rw [drift_reference_error_expansion, map_sub, map_add, map_add, map_smul,
    inner_sub_right, inner_add_right, inner_add_right, real_inner_smul_right,
    sobolevWeighted_inner_laplacian, sobolevDissipation_eq_energy_succ_sub]
  change 2 * (_ + _ + _ - ν * (D - Q)) ≤ referenceErrorGrowth ν R * Q
  unfold referenceErrorGrowth
  change 2 * (_ + _ + _ - ν * (D - Q)) ≤ (2 * ν + K * (2 + 4 * R)) * Q
  have hνD : 0 ≤ ν * D := mul_nonneg hν.le hD
  nlinarith

end
end QuantumAdapter.Obligations
