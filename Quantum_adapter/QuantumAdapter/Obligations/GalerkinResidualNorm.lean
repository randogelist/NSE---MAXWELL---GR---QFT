import QuantumAdapter.Obligations.GalerkinReferencePhase

/-!
# The actual consistency residual bounded by a genuine H0 cutoff tail

The fixed-frequency projected convolution is bilinear on the native H0 space.
Its explicit polynomial frequency bound controls the actual residual without
postulating an infinite-dimensional Sobolev product estimate.
-/
set_option autoImplicit false
set_option Elab.async true
open Set
open scoped BigOperators Topology
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (NSSolution Data SmoothVelocity)

/-- Actual quadratic difference, before taking any norm. -/
theorem projectedTransportCoefficient_difference (k : Frequency) (i : Fin 3)
    (v c : TorusSobolev 0) :
    projectedTransportCoefficient k i v v - projectedTransportCoefficient k i c c =
      projectedTransportCoefficient k i (v - c) v +
        projectedTransportCoefficient k i c (v - c) := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

/-- The fixed-frequency residual is controlled by the literal H0 difference. -/
theorem projectedTransportCoefficient_difference_norm_le (k : Frequency) (i : Fin 3)
    (v c : TorusSobolev 0) :
    ‖projectedTransportCoefficient k i v v - projectedTransportCoefficient k i c c‖ ≤
      projectedTransportMajorant k * ((‖v‖ + ‖c‖) * ‖v - c‖) := by
  rw [projectedTransportCoefficient_difference]
  calc
    _ ≤ ‖projectedTransportCoefficient k i (v - c) v‖ +
        ‖projectedTransportCoefficient k i c (v - c)‖ := norm_add_le _ _
    _ ≤ projectedTransportMajorant k * (‖v - c‖ * ‖v‖) +
        projectedTransportMajorant k * (‖c‖ * ‖v - c‖) :=
      add_le_add (projectedTransportCoefficient_norm_le k i (v - c) v)
        (projectedTransportCoefficient_norm_le k i c (v - c))
    _ = _ := by ring

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- The projected native phase is exactly the existing Hs cutoff, including its mean. -/
theorem reference_phaseSobolev_eq_cutoff (h : NSSolution ν a u p)
    (s N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    phaseSobolev s N (referenceProjection h N t) =
      torusSobolevCutoff s N (referenceSobolevAt h s t ht) := by
  apply Subtype.ext
  funext k i
  simp only [phaseSobolev_coeff, referenceProjection_coeff h N t ht,
    torusSobolevCutoff_coeff, referenceSobolevAt_coeff]
  rfl

/-- The actual projected reference never increases its genuine Hs norm. -/
theorem reference_phaseSobolev_norm_le (h : NSSolution ν a u p)
    (s N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖phaseSobolev s N (referenceProjection h N t)‖ ≤ ‖referenceSobolevAt h s t ht‖ := by
  rw [reference_phaseSobolev_eq_cutoff]
  exact torusSobolevCutoff_norm_le s N (referenceSobolevAt h s t ht)

/-- Every actual residual Sobolev energy is reduced to an H0 tail and a finite frequency sum. -/
theorem referenceResidual_sobolevEnergy_le_h0_difference
    (h : NSSolution ν a u p) (m N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    sobolevEnergy m N (referenceResidualPhase h N t ht) ≤
      432 * ((‖phaseSobolev 0 N (referenceProjection h N t)‖ +
        ‖referenceSobolevAt h 0 t ht‖) *
        ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖) ^ 2 *
          ∑ k ∈ fullModes N, torusSobolevWeight k ^ (2 * m + 4) := by
  let v := phaseSobolev 0 N (referenceProjection h N t)
  let c := referenceSobolevAt h 0 t ht
  let D := (‖v‖ + ‖c‖) * ‖v - c‖
  have hD : 0 ≤ D := mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hpoint (k : Frequency) (hk : k ∈ fullModes N) (i : Fin 3) :
      ‖sobolevWeightedCoeff m (phaseCoeff (referenceResidualPhase h N t ht)) (k, i)‖ ^ 2 ≤
        144 * D ^ 2 * torusSobolevWeight k ^ (2 * m + 4) := by
    rw [sobolevWeightedCoeff_norm_eq, referenceResidualPhase_coeff h N t ht, if_pos hk]
    have hn := projectedTransportCoefficient_difference_norm_le k i v c
    have hh := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le m) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hn (pow_nonneg (torusSobolevWeight_pos k).le m)) 2
    calc
      _ ≤ (torusSobolevWeight k ^ m * (projectedTransportMajorant k * D)) ^ 2 := hh
      _ = _ := by
        unfold projectedTransportMajorant
        rw [show 2 * m + 4 = m + m + 4 by omega, pow_add, pow_add]
        ring
  calc
    _ ≤ ∑ k ∈ fullModes N, ∑ i : Fin 3,
        144 * D ^ 2 * torusSobolevWeight k ^ (2 * m + 4) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.sum_le_sum (fun i hi => hpoint k hk i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Using contraction, the residual bound contains only the full reference norm and its tail. -/
theorem referenceResidual_h3_le_h0_tail (h : NSSolution ν a u p)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    sobolevEnergy 3 N (referenceResidualPhase h N t ht) ≤
      1728 * ‖referenceSobolevAt h 0 t ht‖ ^ 2 *
        ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖ ^ 2 *
          ∑ k ∈ fullModes N, torusSobolevWeight k ^ 10 := by
  have hbase := referenceResidual_sobolevEnergy_le_h0_difference h 3 N t ht
  have hv := reference_phaseSobolev_norm_le h 0 N t ht
  have hD : (‖phaseSobolev 0 N (referenceProjection h N t)‖ +
      ‖referenceSobolevAt h 0 t ht‖) ^ 2 ≤ 4 * ‖referenceSobolevAt h 0 t ht‖ ^ 2 := by
    nlinarith [norm_nonneg (phaseSobolev 0 N (referenceProjection h N t)),
      norm_nonneg (referenceSobolevAt h 0 t ht)]
  have hsum : 0 ≤ ∑ k ∈ fullModes N, torusSobolevWeight k ^ 10 :=
    Finset.sum_nonneg (fun k hk => pow_nonneg (torusSobolevWeight_pos k).le _)
  calc
    _ ≤ _ := hbase
    _ = 432 * (‖phaseSobolev 0 N (referenceProjection h N t)‖ +
        ‖referenceSobolevAt h 0 t ht‖) ^ 2 *
      ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖ ^ 2 *
        ∑ k ∈ fullModes N, torusSobolevWeight k ^ 10 := by norm_num; ring
    _ ≤ _ := by
      have hd := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num))
          (sq_nonneg ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖)) hsum
      convert hd using 1 <;> ring

end
end QuantumAdapter.Obligations
