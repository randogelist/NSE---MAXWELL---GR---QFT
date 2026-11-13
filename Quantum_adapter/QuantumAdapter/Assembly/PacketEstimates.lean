import QuantumAdapter.RegularityContracts
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Quantitative packet estimates from primitive analytic endpoints

The probability measure, distance, energy, and accumulated gradient below use
the actual native phase and Gaussian. The unresolved inputs are explicit local
analytic statements. Neither a forward/reverse packet estimate nor a global
regularity implication is a field of `PacketEstimatePrimitives`.

The scalar integration, exact first-moment selection, exponential comparison,
and assembly into `PacketBounds` have proof bodies in this file.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal

namespace QuantumAdapter.Assembly

noncomputable section

/-- The actual initial Born measure on the intrinsic real phase. -/
def canonicalBornMeasure (N : ℕ) (q₀ : Phase N) : Measure (Phase N) :=
  (phaseVolume N).withDensity
    (fun q => ENNReal.ofReal (bornDensity (canonicalPacket N q₀) q))

/-- The finite inverse-inequality distance appearing in both packet estimates. -/
def packetDistance (N : ℕ) (q r : Phase N) : ℝ :=
  cutoffSobolevFactor N * ‖q - r‖

theorem packetDistance_nonneg (N : ℕ) (q r : Phase N) :
    0 ≤ packetDistance N q r :=
  mul_nonneg (cutoffSobolevFactor_pos N).le (norm_nonneg _)

theorem packetDistance_symm (N : ℕ) (q r : Phase N) :
    packetDistance N q r = packetDistance N r q := by
  simp only [packetDistance, norm_sub_rev]

/-- The actual integrated spatial-gradient observable along one finite orbit. -/
def orbitGradientCost {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q : Phase N) (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, gradientObservable (F.map N s q)

section ProbabilityScalar

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [IsProbabilityMeasure μ]

/-- At the fixed radius one half, the first moment follows by integrating
`d ≤ d² + 1/4`. No totalized-integral or limiting argument is used. -/
theorem packet_integral_distance_le_half {d : α → ℝ}
    (hd : Integrable d μ) (hd2 : Integrable (fun x => d x ^ 2) μ)
    (hmoment : (∫ x, d x ^ 2 ∂μ) ≤ (1 / 4 : ℝ)) :
    (∫ x, d x ∂μ) ≤ (1 / 2 : ℝ) := by
  have hpoint (x : α) : d x ≤ d x ^ 2 + (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (d x - (1 / 2 : ℝ))]
  have hmono := integral_mono hd (hd2.add (integrable_const (1 / 4 : ℝ))) hpoint
  have hbound : (∫ x, d x ∂μ) ≤ (∫ x, d x ^ 2 ∂μ) + (1 / 4 : ℝ) := by
    simpa [integral_add hd2 (integrable_const (1 / 4 : ℝ))] using hmono
  linarith

/-- Exact scalar second-moment integration of a pointwise affine square bound. -/
theorem packet_integral_quadratic_bound {e d : α → ℝ} {a b : ℝ}
    (he : Integrable e μ) (hd : Integrable d μ)
    (hd2 : Integrable (fun x => d x ^ 2) μ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmoment : (∫ x, d x ^ 2 ∂μ) ≤ (1 / 4 : ℝ))
    (hpoint : ∀ x, e x ≤ (a + b * d x) ^ 2) :
    (∫ x, e x ∂μ) ≤ (a + b / 2) ^ 2 := by
  let p : α → ℝ := fun x => a ^ 2 + (2 * a * b) * d x + b ^ 2 * d x ^ 2
  have hp : Integrable p μ :=
    ((integrable_const (a ^ 2)).add (hd.const_mul (2 * a * b))).add
      (hd2.const_mul (b ^ 2))
  have hpval : (∫ x, p x ∂μ) =
      a ^ 2 + (2 * a * b) * (∫ x, d x ∂μ) + b ^ 2 * (∫ x, d x ^ 2 ∂μ) := by
    dsimp [p]
    rw [integral_add ((integrable_const (a ^ 2)).add (hd.const_mul (2 * a * b)))
        (hd2.const_mul (b ^ 2)),
      integral_add (integrable_const (a ^ 2)) (hd.const_mul (2 * a * b))]
    simp [integral_const_mul]
  have hmono : (∫ x, e x ∂μ) ≤ ∫ x, p x ∂μ := by
    apply integral_mono he hp
    intro x
    calc
      e x ≤ (a + b * d x) ^ 2 := hpoint x
      _ = p x := by dsimp [p]; ring
  rw [hpval] at hmono
  have hfirst := packet_integral_distance_le_half hd hd2 hmoment
  have hcross := mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ 2 * a * b by positivity)
  have hquad := mul_le_mul_of_nonneg_left hmoment (sq_nonneg b)
  nlinarith

/-- Exact simultaneous control of integrated gradient and initial displacement.
The selected point is supplied by the first moment theorem, not a minimizer. -/
theorem exists_joint_packet_control {g d : α → ℝ} {L : ℝ}
    (hg : Integrable g μ) (hd2 : Integrable (fun x => d x ^ 2) μ)
    (hgnonneg : ∀ x, 0 ≤ g x)
    (hgmean : (∫ x, g x ∂μ) ≤ L)
    (hdmean : (∫ x, d x ^ 2 ∂μ) ≤ (1 / 4 : ℝ)) :
    ∃ x, g x ≤ L + (1 / 4 : ℝ) ∧
      d x ≤ Real.sqrt (L + (1 / 4 : ℝ)) := by
  obtain ⟨x, hx⟩ := exists_le_integral (hg.add hd2)
  rw [integral_add hg hd2] at hx
  have hsum : g x + d x ^ 2 ≤ L + (1 / 4 : ℝ) :=
    hx.trans (add_le_add hgmean hdmean)
  refine ⟨x, ?_, ?_⟩
  · nlinarith [sq_nonneg (d x)]
  · apply Real.le_sqrt_of_sq_le
    linarith [hgnonneg x]

end ProbabilityScalar

/-- Analytic frontier for the actual packet construction.

`central_cost_bound` is the time-integrated Fourier gradient embedding.
`mean_cost_bound` is the time-integrated probability Cauchy--Schwarz/Fubini
estimate. They concern the native gradient cost, not the desired energy
comparison. The relative and tame fields are per-trajectory inequalities.
No inhabitant is claimed in this file.
-/
structure PacketEstimatePrimitives {ν : ℝ} (F : PhaseFlow ν)
    (Cemb C3 : ℝ) : Prop where
  embedding_pos : 0 < Cemb
  tame_pos : 0 < C3
  probability : ∀ N q₀, IsProbabilityMeasure (canonicalBornMeasure N q₀)
  distance_integrable : ∀ N, 1 ≤ N → ∀ q₀,
    Integrable (fun q => packetDistance N q q₀) (canonicalBornMeasure N q₀)
  distance_sq_integrable : ∀ N, 1 ≤ N → ∀ q₀,
    Integrable (fun q => packetDistance N q q₀ ^ 2) (canonicalBornMeasure N q₀)
  distance_sq_mean : ∀ N, 1 ≤ N → ∀ q₀,
    (∫ q, packetDistance N q q₀ ^ 2 ∂canonicalBornMeasure N q₀) ≤ (1 / 4 : ℝ)
  energy_integrable : ∀ N, 1 ≤ N → ∀ q₀ t, 0 ≤ t →
    Integrable (fun q => energy3 N (F.map N t q)) (canonicalBornMeasure N q₀)
  energy_conjugacy : ∀ N, 1 ≤ N → ∀ q₀ t, 0 ≤ t →
    quantumEnergy F N q₀ t =
      ∫ q, energy3 N (F.map N t q) ∂canonicalBornMeasure N q₀
  admissible : ∀ N, 1 ≤ N → ∀ q₀ t, 0 ≤ t → quantumAdmissible F N q₀ t
  initial_triangle : ∀ N (q r : Phase N),
    Real.sqrt (energy3 N q) ≤ Real.sqrt (energy3 N r) + packetDistance N q r
  relative : ∀ N (q r : Phase N) t, 0 ≤ t →
    Real.sqrt (energy3 N (F.map N t q)) ≤
      Real.sqrt (energy3 N (F.map N t r)) +
        packetDistance N q r * Real.exp (orbitGradientCost F N r t)
  tame : ∀ N (q : Phase N) t, 0 ≤ t →
    Real.sqrt (energy3 N (F.map N t q)) ≤
      Real.sqrt (energy3 N q) * Real.exp (C3 * orbitGradientCost F N q t)
  cost_nonneg : ∀ N (q : Phase N) t, 0 ≤ t → 0 ≤ orbitGradientCost F N q t
  cost_mono : ∀ N (q : Phase N) t T, 0 ≤ t → t ≤ T →
    orbitGradientCost F N q t ≤ orbitGradientCost F N q T
  cost_integrable : ∀ N, 1 ≤ N → ∀ q₀ T, 0 < T →
    Integrable (fun q => orbitGradientCost F N q T) (canonicalBornMeasure N q₀)
  central_cost_bound : ∀ N, 1 ≤ N → ∀ q₀ T C, 0 < T → 0 ≤ C →
    (∀ t, 0 ≤ t → t ≤ T → energy3 N (F.map N t q₀) ≤ C) →
    orbitGradientCost F N q₀ T ≤ Cemb * T * Real.sqrt C
  mean_cost_bound : ∀ N, 1 ≤ N → ∀ q₀ T C, 0 < T → 0 ≤ C →
    (∀ t, 0 ≤ t → t ≤ T → quantumEnergy F N q₀ t ≤ C) →
    (∫ q, orbitGradientCost F N q T ∂canonicalBornMeasure N q₀) ≤
      Cemb * T * Real.sqrt C

variable {ν Cemb C3 : ℝ} {F : PhaseFlow ν}

/-- The native forward constant, derived by explicit second-moment integration. -/
theorem forwardPacketBound_of_primitives (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) (T C : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C)
    (hcentral : ∀ t, 0 ≤ t → t ≤ T → energy3 N (F.map N t q₀) ≤ C)
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    quantumEnergy F N q₀ t ≤ forwardPacketBound Cemb T C := by
  letI : IsProbabilityMeasure (canonicalBornMeasure N q₀) := H.probability N q₀
  let L := Cemb * T * Real.sqrt C
  have hcost : orbitGradientCost F N q₀ t ≤ L :=
    (H.cost_mono N q₀ t T ht htT).trans
      (H.central_cost_bound N hN q₀ T C hT hC hcentral)
  have hpoint (q : Phase N) : energy3 N (F.map N t q) ≤
      (Real.sqrt C + Real.exp L * packetDistance N q q₀) ^ 2 := by
    apply (Real.sqrt_le_iff.mp ?_).2
    have hreference := Real.sqrt_le_sqrt (hcentral t ht htT)
    have hfluctuation := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hcost) (packetDistance_nonneg N q q₀)
    calc
      Real.sqrt (energy3 N (F.map N t q)) ≤
          Real.sqrt (energy3 N (F.map N t q₀)) +
            packetDistance N q q₀ * Real.exp (orbitGradientCost F N q₀ t) :=
        H.relative N q q₀ t ht
      _ ≤ Real.sqrt C + Real.exp L * packetDistance N q q₀ := by
        nlinarith
  rw [H.energy_conjugacy N hN q₀ t ht]
  have hbound := packet_integral_quadratic_bound
    (H.energy_integrable N hN q₀ t ht) (H.distance_integrable N hN q₀)
    (H.distance_sq_integrable N hN q₀) (Real.sqrt_nonneg C)
    (Real.exp_pos L).le (H.distance_sq_mean N hN q₀) hpoint
  simpa [forwardPacketBound, L, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hbound

/-- The native reverse constant, using one selected reference trajectory. -/
theorem reversePacketBound_of_primitives (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) (T A C : ℝ)
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hinitial : energy3 N q₀ ≤ A ^ 2)
    (hquantum : ∀ t, 0 ≤ t → t ≤ T → quantumEnergy F N q₀ t ≤ C)
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    energy3 N (F.map N t q₀) ≤ reversePacketBound Cemb C3 T A C := by
  letI : IsProbabilityMeasure (canonicalBornMeasure N q₀) := H.probability N q₀
  let L := Cemb * T * Real.sqrt C
  let S := L + (1 / 4 : ℝ)
  obtain ⟨q, hqcost, hqdist⟩ := exists_joint_packet_control
    (H.cost_integrable N hN q₀ T hT) (H.distance_sq_integrable N hN q₀)
    (fun q => H.cost_nonneg N q T hT.le)
    (H.mean_cost_bound N hN q₀ T C hT hC hquantum)
    (H.distance_sq_mean N hN q₀)
  have hcost : orbitGradientCost F N q t ≤ S :=
    (H.cost_mono N q t T ht htT).trans hqcost
  have hdist : packetDistance N q₀ q ≤ Real.sqrt S := by
    rw [packetDistance_symm]
    exact hqdist
  have hrootinitial : Real.sqrt (energy3 N q₀) ≤ A :=
    Real.sqrt_le_iff.mpr ⟨hA, hinitial⟩
  have hqinitial : Real.sqrt (energy3 N q) ≤ A + Real.sqrt S :=
    (H.initial_triangle N q q₀).trans (add_le_add hrootinitial hqdist)
  have htame : Real.sqrt (energy3 N (F.map N t q)) ≤
      (A + Real.sqrt S) * Real.exp (C3 * S) := by
    apply (H.tame N q t ht).trans
    exact mul_le_mul hqinitial
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcost H.tame_pos.le))
      (Real.exp_pos _).le (add_nonneg hA (Real.sqrt_nonneg S))
  have hrelativeTerm : packetDistance N q₀ q * Real.exp (orbitGradientCost F N q t) ≤
      Real.sqrt S * Real.exp S :=
    mul_le_mul hdist (Real.exp_le_exp.mpr hcost)
      (Real.exp_pos _).le (Real.sqrt_nonneg S)
  have hroot : Real.sqrt (energy3 N (F.map N t q₀)) ≤
      (A + Real.sqrt S) * Real.exp (C3 * S) + Real.sqrt S * Real.exp S :=
    (H.relative N q₀ q t ht).trans (add_le_add htame hrelativeTerm)
  have hfinal := (Real.sqrt_le_iff.mp hroot).2
  simpa only [reversePacketBound, packetGradientBudget, L, S,
    add_comm (1 / 4 : ℝ) (Cemb * T * Real.sqrt C)] using hfinal

/-- Deterministic assembly: every quantitative packet field has a proof body. -/
theorem packetBounds_of_scalar_primitives (H : PacketEstimatePrimitives F Cemb C3) :
    PacketBounds F Cemb C3 where
  embedding_pos := H.embedding_pos
  tame_pos := H.tame_pos
  admissible := H.admissible
  forward_estimate := forwardPacketBound_of_primitives H
  reverse_estimate := reversePacketBound_of_primitives H

end

end QuantumAdapter.Assembly
