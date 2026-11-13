import QuantumAdapter.RegularityContracts
import QuantumAdapter.Assembly.Fourier
import QuantumAdapter.Assembly.Gaussian
import QuantumAdapter.Assembly.Admissibility
import QuantumAdapter.Assembly.FlowContinuity
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
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

theorem canonicalBornDensity_measurable (N : ℕ) (q₀ : Phase N) :
    Measurable (fun q => ENNReal.ofReal (bornDensity (canonicalPacket N q₀) q)) := by
  have h : Continuous (fun q => bornDensity (canonicalPacket N q₀) q) := by
    unfold bornDensity canonicalPacket
    fun_prop
  exact h.measurable.ennreal_ofReal

instance canonicalBornMeasure_isProbability (N : ℕ) (q₀ : Phase N) :
    IsProbabilityMeasure (canonicalBornMeasure N q₀) where
  measure_univ := by
    unfold canonicalBornMeasure
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (canonicalPacket_density_integrable N q₀)
        (Filter.Eventually.of_forall (bornDensity_nonneg (canonicalPacket N q₀))),
      canonicalPacket_normalized]
    norm_num

theorem integrable_canonicalBornMeasure_iff (N : ℕ) (q₀ : Phase N)
    (f : Phase N → ℝ) :
    Integrable f (canonicalBornMeasure N q₀) ↔
      Integrable (fun q => f q * bornDensity (canonicalPacket N q₀) q) (phaseVolume N) := by
  unfold canonicalBornMeasure
  rw [integrable_withDensity_iff (canonicalBornDensity_measurable N q₀)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (bornDensity_nonneg (canonicalPacket N q₀) _)]

theorem integral_canonicalBornMeasure (N : ℕ) (q₀ : Phase N) (f : Phase N → ℝ) :
    (∫ q, f q ∂canonicalBornMeasure N q₀) =
      ∫ q, f q * bornDensity (canonicalPacket N q₀) q ∂phaseVolume N := by
  unfold canonicalBornMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (canonicalBornDensity_measurable N q₀)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [ENNReal.toReal_ofReal (bornDensity_nonneg (canonicalPacket N q₀) q),
    smul_eq_mul, mul_comm]

theorem canonicalBornMeasure_centered_moment_integrable (N : ℕ) (q₀ : Phase N) (k : ℕ) :
    Integrable (fun q => ‖q - q₀‖ ^ k) (canonicalBornMeasure N q₀) :=
  (integrable_canonicalBornMeasure_iff N q₀ _).2
    (canonicalPacket_centered_moment_integrable N q₀ k)

/-- The finite inverse-inequality distance appearing in both packet estimates. -/
def packetDistance (N : ℕ) (q r : Phase N) : ℝ :=
  cutoffSobolevFactor N * ‖q - r‖

theorem packetDistance_nonneg (N : ℕ) (q r : Phase N) :
    0 ≤ packetDistance N q r :=
  mul_nonneg (cutoffSobolevFactor_pos N).le (norm_nonneg _)

theorem packetDistance_symm (N : ℕ) (q r : Phase N) :
    packetDistance N q r = packetDistance N r q := by
  simp only [packetDistance, norm_sub_rev]

theorem packetDistance_integrable (N : ℕ) (q₀ : Phase N) :
    Integrable (fun q => packetDistance N q q₀) (canonicalBornMeasure N q₀) := by
  have h := (canonicalBornMeasure_centered_moment_integrable N q₀ 1).const_mul
    (cutoffSobolevFactor N)
  simpa only [pow_one, packetDistance] using h

theorem packetDistance_sq_integrable (N : ℕ) (q₀ : Phase N) :
    Integrable (fun q => packetDistance N q q₀ ^ 2) (canonicalBornMeasure N q₀) := by
  have h := (canonicalBornMeasure_centered_moment_integrable N q₀ 2).const_mul
    (cutoffSobolevFactor N ^ 2)
  simpa only [packetDistance, mul_pow] using h

theorem packetDistance_sq_mean (N : ℕ) (q₀ : Phase N) :
    (∫ q, packetDistance N q q₀ ^ 2 ∂canonicalBornMeasure N q₀) =
      (((N : ℝ) + 1) ^ 2)⁻¹ := by
  rw [integral_canonicalBornMeasure]
  have hfun :
      (fun q => packetDistance N q q₀ ^ 2 * bornDensity (canonicalPacket N q₀) q) =
      (fun q => cutoffSobolevFactor N ^ 2 *
        (‖q - q₀‖ ^ 2 * bornDensity (canonicalPacket N q₀) q)) := by
    funext q
    unfold packetDistance
    ring
  rw [hfun, integral_const_mul, canonicalPacket_second_moment]
  have hw : cutoffSobolevFactor N ≠ 0 := ne_of_gt (cutoffSobolevFactor_pos N)
  have hd : (phaseDimension N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (phase_finrank_pos N))
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  unfold canonicalScale
  rw [inv_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (phaseDimension N))]
  field_simp [hw, hd, hN]
  <;> ring

theorem packetDistance_sq_mean_le_quarter (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) :
    (∫ q, packetDistance N q q₀ ^ 2 ∂canonicalBornMeasure N q₀) ≤ (1 / 4 : ℝ) := by
  rw [packetDistance_sq_mean]
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (4 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  have hdenpos : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  have hdiv : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
    apply (div_le_div_iff₀ hdenpos (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  simpa only [one_div] using hdiv

theorem sqrt_energy3_le_reference_add_packetDistance (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N q) ≤ Real.sqrt (energy3 N r) + packetDistance N q r := by
  change Real.sqrt (energy3 N q) ≤
    Real.sqrt (energy3 N r) + cutoffSobolevFactor N * ‖q - r‖
  calc
    Real.sqrt (energy3 N q) ≤
        Real.sqrt (energy3 N (q - r)) + Real.sqrt (energy3 N r) :=
      sqrt_energy3_le_add N q r
    _ ≤ cutoffSobolevFactor N * ‖q - r‖ + Real.sqrt (energy3 N r) :=
      add_le_add_right (sqrt_energy3_le_cutoffSobolevFactor_mul_norm N (q - r)) _
    _ = Real.sqrt (energy3 N r) + cutoffSobolevFactor N * ‖q - r‖ := add_comm _ _

/-- The actual integrated spatial-gradient observable along one finite orbit. -/
def orbitGradientCost {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q : Phase N) (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, gradientObservable (F.map N s q)

section ProbabilityScalar

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [IsProbabilityMeasure μ]

/-- Probability Cauchy--Schwarz, proved by integrating the square centered at
the actual first moment. Both integrability hypotheses are explicit. -/
theorem packet_integral_sq_le {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let m := ∫ x, f x ∂μ
  let p : α → ℝ := fun x => f x ^ 2 - (2 * m) * f x + m ^ 2
  have hpnonneg (x : α) : 0 ≤ p x := by
    dsimp [p]
    nlinarith [sq_nonneg (f x - m)]
  have hpval : (∫ x, p x ∂μ) = (∫ x, f x ^ 2 ∂μ) - m ^ 2 := by
    calc
      (∫ x, p x ∂μ) = (∫ x, f x ^ 2 ∂μ) - (2 * m) * (∫ x, f x ∂μ) + m ^ 2 := by
        dsimp [p]
        rw [integral_add
            (f := fun x => f x ^ 2 - (2 * m) * f x) (g := fun _ : α => m ^ 2)
            (hf2.sub (hf.const_mul (2 * m))) (integrable_const (m ^ 2)),
          integral_sub (f := fun x => f x ^ 2) (g := fun x => (2 * m) * f x)
            hf2 (hf.const_mul (2 * m))]
        simp [integral_const_mul]
      _ = (∫ x, f x ^ 2 ∂μ) - m ^ 2 := by dsimp [m]; ring
  have hnonneg := MeasureTheory.integral_nonneg (μ := μ) (f := p) hpnonneg
  rw [hpval] at hnonneg
  dsimp [m] at hnonneg
  linarith

theorem packet_integrable_sqrt {e : α → ℝ}
    (he : Integrable e μ) (he0 : ∀ x, 0 ≤ e x) :
    Integrable (fun x => Real.sqrt (e x)) μ := by
  apply (he.add (integrable_const (1 : ℝ))).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable he.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖Real.sqrt (e x)‖ ≤ e x + 1
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg (e x))]
  nlinarith [Real.sq_sqrt (he0 x), Real.sqrt_nonneg (e x),
    sq_nonneg (Real.sqrt (e x) - 1)]

/-- Exact first-moment/square-root estimate, including zero expected energy. -/
theorem packet_integral_sqrt_le {e : α → ℝ}
    (he : Integrable e μ) (he0 : ∀ x, 0 ≤ e x) :
    (∫ x, Real.sqrt (e x) ∂μ) ≤ Real.sqrt (∫ x, e x ∂μ) := by
  have hr := packet_integrable_sqrt he he0
  have hr2 : Integrable (fun x => Real.sqrt (e x) ^ 2) μ :=
    he.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (he0 x)).symm))
  have hvariance := packet_integral_sq_le hr hr2
  have hsame : (∫ x, Real.sqrt (e x) ^ 2 ∂μ) = ∫ x, e x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => Real.sq_sqrt (he0 x)))
  rw [hsame] at hvariance
  exact Real.le_sqrt_of_sq_le hvariance

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
    change (∫ x, d x ∂μ) ≤ ∫ x, d x ^ 2 + (1 / 4 : ℝ) ∂μ at hmono
    rw [integral_add (f := fun x => d x ^ 2) (g := fun _ : α => (1 / 4 : ℝ))
      hd2 (integrable_const (1 / 4 : ℝ))] at hmono
    simpa using hmono
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
    rw [integral_add (f := fun x => a ^ 2 + (2 * a * b) * d x)
        (g := fun x => b ^ 2 * d x ^ 2)
        ((integrable_const (a ^ 2)).add (hd.const_mul (2 * a * b)))
        (hd2.const_mul (b ^ 2)),
      integral_add (f := fun _ : α => a ^ 2) (g := fun x => (2 * a * b) * d x)
        (integrable_const (a ^ 2)) (hd.const_mul (2 * a * b))]
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
  simp only [Pi.add_apply] at hx
  rw [integral_add hg hd2] at hx
  have hsum : g x + d x ^ 2 ≤ L + (1 / 4 : ℝ) :=
    hx.trans (add_le_add hgmean hdmean)
  refine ⟨x, ?_, ?_⟩
  · nlinarith [sq_nonneg (d x)]
  · apply Real.le_sqrt_of_sq_le
    linarith [hgnonneg x]

end ProbabilityScalar

/-- Analytic frontier for the actual packet construction.

The remaining integration premise is actual gradient integrability on the
time/phase product. Cauchy--Schwarz, Fubini, and the resulting mean-cost bound
are proved below. The relative and tame fields are per-trajectory
inequalities. No inhabitant of this residual structure is claimed here.
-/
structure PacketEstimatePrimitives {ν : ℝ} (F : PhaseFlow ν)
    (Cemb C3 : ℝ) : Prop where
  embedding_pos : 0 < Cemb
  tame_pos : 0 < C3
  transport : PhaseTransportLaws F
  energy_integrable : ∀ N, 1 ≤ N → ∀ q₀ t, 0 ≤ t →
    Integrable (fun q => energy3 N (F.map N t q)) (canonicalBornMeasure N q₀)
  admissible : ∀ N, 1 ≤ N → ∀ q₀ t, 0 ≤ t → quantumAdmissible F N q₀ t
  relative_l2 : ∀ N (q r : Phase N) t, 0 ≤ t →
    ‖F.map N t q - F.map N t r‖ ≤
      ‖q - r‖ * Real.exp (orbitGradientCost F N r t)
  tame : ∀ N (q : Phase N) t, 0 ≤ t →
    Real.sqrt (energy3 N (F.map N t q)) ≤
      Real.sqrt (energy3 N q) * Real.exp (C3 * orbitGradientCost F N q t)
  gradient_nonneg : ∀ N (q : Phase N), 0 ≤ gradientObservable q
  gradient_bound : ∀ N (q : Phase N),
    gradientObservable q ≤ Cemb * Real.sqrt (energy3 N q)
  time_gradient_integrable : ∀ N (q : Phase N) T, 0 ≤ T →
    IntervalIntegrable (fun s => gradientObservable (F.map N s q)) volume 0 T
  gradient_product_integrable : ∀ N, 1 ≤ N → ∀ q₀ T, 0 < T →
    Integrable (fun z : ℝ × Phase N => gradientObservable (F.map N z.1 z.2))
      ((volume.restrict (Ioc 0 T)).prod (canonicalBornMeasure N q₀))

variable {ν Cemb C3 : ℝ} {F : PhaseFlow ν}

theorem PacketEstimatePrimitives.energy_conjugacy (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    quantumEnergy F N q₀ t =
      ∫ q, energy3 N (F.map N t q) ∂canonicalBornMeasure N q₀ := by
  have hi := (integrable_canonicalBornMeasure_iff N q₀ _).1
    (H.energy_integrable N hN q₀ t ht)
  rw [quantumEnergy_conjugacy F H.transport N q₀ t hi]
  exact (integral_canonicalBornMeasure N q₀ _).symm

theorem PacketEstimatePrimitives.relative (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (q r : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (energy3 N (F.map N t q)) ≤
      Real.sqrt (energy3 N (F.map N t r)) +
        packetDistance N q r * Real.exp (orbitGradientCost F N r t) := by
  have htriangle := sqrt_energy3_le_reference_add_packetDistance N
    (F.map N t q) (F.map N t r)
  have hrelative := mul_le_mul_of_nonneg_left (H.relative_l2 N q r t ht)
    (cutoffSobolevFactor_pos N).le
  have hdist : packetDistance N (F.map N t q) (F.map N t r) ≤
      packetDistance N q r * Real.exp (orbitGradientCost F N r t) := by
    change cutoffSobolevFactor N * ‖F.map N t q - F.map N t r‖ ≤
      (cutoffSobolevFactor N * ‖q - r‖) * Real.exp (orbitGradientCost F N r t)
    simpa only [mul_assoc] using hrelative
  exact htriangle.trans (add_le_add_left hdist _)

theorem PacketEstimatePrimitives.cost_nonneg (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (q : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ orbitGradientCost F N q t :=
  intervalIntegral.integral_nonneg_of_forall ht
    (fun s => H.gradient_nonneg N (F.map N s q))

theorem PacketEstimatePrimitives.cost_mono (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (q : Phase N) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    orbitGradientCost F N q t ≤ orbitGradientCost F N q T :=
  intervalIntegral.integral_mono_interval le_rfl ht htT
    (Filter.Eventually.of_forall (fun s => H.gradient_nonneg N (F.map N s q)))
    (H.time_gradient_integrable N q T (ht.trans htT))

theorem PacketEstimatePrimitives.central_cost_bound (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (_hN : 1 ≤ N) (q₀ : Phase N) (T C : ℝ)
    (hT : 0 < T) (_hC : 0 ≤ C)
    (hcentral : ∀ t, 0 ≤ t → t ≤ T → energy3 N (F.map N t q₀) ≤ C) :
    orbitGradientCost F N q₀ T ≤ Cemb * T * Real.sqrt C := by
  have hmono := intervalIntegral.integral_mono_on hT.le
    (H.time_gradient_integrable N q₀ T hT.le)
    (intervalIntegrable_const (c := Cemb * Real.sqrt C))
    (fun s hs => (H.gradient_bound N (F.map N s q₀)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hcentral s hs.1 hs.2))
        H.embedding_pos.le))
  simpa [orbitGradientCost, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hmono

theorem PacketEstimatePrimitives.cost_integrable (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) (T : ℝ) (hT : 0 < T) :
    Integrable (fun q => orbitGradientCost F N q T) (canonicalBornMeasure N q₀) := by
  have h := (H.gradient_product_integrable N hN q₀ T hT).integral_prod_right
  simpa only [orbitGradientCost, intervalIntegral.integral_of_le hT.le] using h

theorem PacketEstimatePrimitives.mean_cost_bound (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) (T C : ℝ)
    (hT : 0 < T) (_hC : 0 ≤ C)
    (hquantum : ∀ t, 0 ≤ t → t ≤ T → quantumEnergy F N q₀ t ≤ C) :
    (∫ q, orbitGradientCost F N q T ∂canonicalBornMeasure N q₀) ≤
      Cemb * T * Real.sqrt C := by
  have hp := H.gradient_product_integrable N hN q₀ T hT
  have htime : (∫ s in Ioc 0 T, ∫ q, gradientObservable (F.map N s q)
      ∂canonicalBornMeasure N q₀) ≤ ∫ _s in Ioc 0 T, Cemb * Real.sqrt C := by
    apply integral_mono_ae hp.integral_prod_left (integrable_const _)
    filter_upwards [hp.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hsrange
    have he := H.energy_integrable N hN q₀ s hsrange.1.le
    have he0 (q : Phase N) : 0 ≤ energy3 N (F.map N s q) := energy3_nonneg N _
    have hroot := packet_integrable_sqrt he he0
    have hgrad := integral_mono hs (hroot.const_mul Cemb)
      (fun q => H.gradient_bound N (F.map N s q))
    rw [integral_const_mul] at hgrad
    have hmean : (∫ q, energy3 N (F.map N s q) ∂canonicalBornMeasure N q₀) ≤ C := by
      rw [← H.energy_conjugacy N hN q₀ s hsrange.1.le]
      exact hquantum s hsrange.1.le hsrange.2
    exact hgrad.trans (mul_le_mul_of_nonneg_left
      ((packet_integral_sqrt_le he he0).trans (Real.sqrt_le_sqrt hmean)) H.embedding_pos.le)
  calc
    (∫ q, orbitGradientCost F N q T ∂canonicalBornMeasure N q₀) =
        ∫ s in Ioc 0 T, ∫ q, gradientObservable (F.map N s q)
          ∂canonicalBornMeasure N q₀ := by
      simp only [orbitGradientCost, intervalIntegral.integral_of_le hT.le]
      exact (integral_integral_swap hp).symm
    _ ≤ ∫ _s in Ioc 0 T, Cemb * Real.sqrt C := htime
    _ = Cemb * T * Real.sqrt C := by
      rw [← intervalIntegral.integral_of_le hT.le]
      simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- The native forward constant, derived by explicit second-moment integration. -/
theorem forwardPacketBound_of_primitives (H : PacketEstimatePrimitives F Cemb C3)
    (N : ℕ) (hN : 1 ≤ N) (q₀ : Phase N) (T C : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C)
    (hcentral : ∀ t, 0 ≤ t → t ≤ T → energy3 N (F.map N t q₀) ≤ C)
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    quantumEnergy F N q₀ t ≤ forwardPacketBound Cemb T C := by
  let L := Cemb * T * Real.sqrt C
  have hcost : orbitGradientCost F N q₀ t ≤ L :=
    (H.cost_mono N q₀ t T ht htT).trans
      (H.central_cost_bound N hN q₀ T C hT hC hcentral)
  have hpoint (q : Phase N) : energy3 N (F.map N t q) ≤
      (Real.sqrt C + Real.exp L * packetDistance N q q₀) ^ 2 := by
    suffices hroot : Real.sqrt (energy3 N (F.map N t q)) ≤
        Real.sqrt C + Real.exp L * packetDistance N q q₀ by
      exact (Real.sqrt_le_iff.mp hroot).2
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
    (H.energy_integrable N hN q₀ t ht) (packetDistance_integrable N q₀)
    (packetDistance_sq_integrable N q₀) (Real.sqrt_nonneg C)
    (Real.exp_pos L).le (packetDistance_sq_mean_le_quarter N hN q₀) hpoint
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
  let L := Cemb * T * Real.sqrt C
  let S := L + (1 / 4 : ℝ)
  obtain ⟨q, hqcost, hqdist⟩ := exists_joint_packet_control
    (H.cost_integrable N hN q₀ T hT) (packetDistance_sq_integrable N q₀)
    (fun q => H.cost_nonneg N q T hT.le)
    (H.mean_cost_bound N hN q₀ T C hT hC hquantum)
    (packetDistance_sq_mean_le_quarter N hN q₀)
  have hcost : orbitGradientCost F N q t ≤ S :=
    (H.cost_mono N q t T ht htT).trans hqcost
  have hdist : packetDistance N q₀ q ≤ Real.sqrt S := by
    rw [packetDistance_symm]
    exact hqdist
  have hrootinitial : Real.sqrt (energy3 N q₀) ≤ A :=
    Real.sqrt_le_iff.mpr ⟨hA, hinitial⟩
  have hqinitial : Real.sqrt (energy3 N q) ≤ A + Real.sqrt S :=
    (sqrt_energy3_le_reference_add_packetDistance N q q₀).trans
      (add_le_add hrootinitial hqdist)
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

theorem canonicalBornMeasure_raw_moment_integrable (N : ℕ) (q₀ : Phase N) (k : ℕ) :
    Integrable (fun q => ‖q‖ ^ k) (canonicalBornMeasure N q₀) :=
  (integrable_canonicalBornMeasure_iff N q₀ _).2
    (canonicalPacket_raw_moment_integrable N q₀ k)

theorem packet_energy_integrable_of_nonneg_viscosity {ν : ℝ}
    (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (N : ℕ) (q₀ : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun q => energy3 N (F.map N t q)) (canonicalBornMeasure N q₀) := by
  apply (integrable_canonicalBornMeasure_iff N q₀ _).2
  exact canonicalPacket_observableIntegrable_of_quadratic_bound N q₀
    ((continuous_energy3 N).comp (hd N t).continuous)
    (fun q => energy3_nonneg N (F.map N t q))
    (phaseFlow_energy3_le_quadratic hν F N t ht)

theorem packet_gradient_product_integrable {ν : ℝ}
    (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (hjoint : ∀ N, Measurable (fun z : ℝ × Phase N => F.map N z.1 z.2))
    (N : ℕ) (q₀ : Phase N) (T : ℝ) (_hT : 0 < T) :
    Integrable (fun z : ℝ × Phase N => gradientObservable (F.map N z.1 z.2))
      ((volume.restrict (Ioc 0 T)).prod (canonicalBornMeasure N q₀)) := by
  have hraw : Integrable (fun q : Phase N => ‖q‖) (canonicalBornMeasure N q₀) := by
    simpa only [pow_one] using canonicalBornMeasure_raw_moment_integrable N q₀ 1
  have hmajorant := (hraw.const_mul
    (gradientEmbeddingConstant * cutoffSobolevFactor N)).comp_snd
      (volume.restrict (Ioc 0 T))
  apply hmajorant.mono'
    (((continuous_gradientObservable N).measurable.comp (hjoint N)).aestronglyMeasurable)
  have htime : ∀ᵐ z : ℝ × Phase N
      ∂((volume.restrict (Ioc 0 T)).prod (canonicalBornMeasure N q₀)), z.1 ∈ Ioc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Filter.Eventually.of_forall (fun _q => hs)
  filter_upwards [htime] with z hz
  change ‖gradientObservable (F.map N z.1 z.2)‖ ≤
    (gradientEmbeddingConstant * cutoffSobolevFactor N) * ‖z.2‖
  rw [Real.norm_of_nonneg (gradientObservable_nonneg N (F.map N z.1 z.2))]
  have hroot : Real.sqrt (energy3 N (F.map N z.1 z.2)) ≤
      cutoffSobolevFactor N * ‖z.2‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (cutoffSobolevFactor_pos N).le (norm_nonneg _), ?_⟩
    simpa only [mul_pow] using phaseFlow_energy3_le_quadratic hν F N z.1 hz.1.le z.2
  exact (gradientObservable_le_sqrt_energy3 N (F.map N z.1 z.2)).trans
    ((mul_le_mul_of_nonneg_left hroot gradientEmbeddingConstant_pos.le).trans_eq
      (mul_assoc _ _ _).symm)

/-- All packet integration/domain obligations follow from actual flow geometry.
Only the per-orbit relative-L2 and high-order tame estimates remain as analytic
energy inequalities, alongside the displayed differential/Jacobian hypotheses.
The gradient continuity and time-integrability endpoints are native theorems.
-/
theorem packetEstimatePrimitives_of_jacobian {ν C3 : ℝ}
    (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (hC3 : 0 < C3)
    (hrelative : ∀ N (q r : Phase N) t, 0 ≤ t →
      ‖F.map N t q - F.map N t r‖ ≤
        ‖q - r‖ * Real.exp (orbitGradientCost F N r t))
    (htame : ∀ N (q : Phase N) t, 0 ≤ t →
      Real.sqrt (energy3 N (F.map N t q)) ≤
        Real.sqrt (energy3 N q) * Real.exp (C3 * orbitGradientCost F N q t)) :
    PacketEstimatePrimitives F gradientEmbeddingConstant C3 where
  embedding_pos := gradientEmbeddingConstant_pos
  tame_pos := hC3
  transport := phaseTransportLaws_of_jacobian F hd hdet
  energy_integrable := fun N _hN q₀ t ht =>
    packet_energy_integrable_of_nonneg_viscosity hν F hd N q₀ t ht
  admissible := fun N _hN q₀ t ht =>
    transportedPacket_quantumAdmissible_of_jacobian hν F hd hdet N q₀ t ht
  relative_l2 := hrelative
  tame := htame
  gradient_nonneg := gradientObservable_nonneg
  gradient_bound := gradientObservable_le_sqrt_energy3
  time_gradient_integrable := fun N q T _hT => intervalIntegrable_gradientObservable F N q 0 T
  gradient_product_integrable := fun N _hN q₀ T hT =>
    packet_gradient_product_integrable hν F
      (fun M => measurable_phaseFlow_uncurry_of_differentiable hν F M (hd M)) N q₀ T hT

theorem packetBounds_of_jacobian {ν C3 : ℝ}
    (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (hC3 : 0 < C3)
    (hrelative : ∀ N (q r : Phase N) t, 0 ≤ t →
      ‖F.map N t q - F.map N t r‖ ≤
        ‖q - r‖ * Real.exp (orbitGradientCost F N r t))
    (htame : ∀ N (q : Phase N) t, 0 ≤ t →
      Real.sqrt (energy3 N (F.map N t q)) ≤
        Real.sqrt (energy3 N q) * Real.exp (C3 * orbitGradientCost F N q t)) :
    PacketBounds F gradientEmbeddingConstant C3 :=
  packetBounds_of_scalar_primitives
    (packetEstimatePrimitives_of_jacobian hν F hd hdet hC3 hrelative htame)

end

end QuantumAdapter.Assembly
