import QuantumAdapter.Dynamics
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma

/-!
The canonical packet is normalized on the intrinsic real phase volume.
These proofs apply to the actual `canonicalPacket`; no Gaussian moment or
normalization certificate is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory

namespace QuantumAdapter

noncomputable section

theorem phaseVolume_eq_volume (N : ℕ) :
    phaseVolume N = (volume : Measure (Phase N)) :=
  (stdOrthonormalBasis ℝ (Phase N)).addHaar_eq_volume

theorem canonicalPacket_continuous (N : ℕ) (q₀ : Phase N) :
    Continuous (canonicalPacket N q₀) := by
  unfold canonicalPacket
  fun_prop

theorem canonicalPacket_bornDensity (N : ℕ) (q₀ q : Phase N) :
    bornDensity (canonicalPacket N q₀) q = gaussianAmplitude N ^ 2 *
      Real.exp (-‖q - q₀‖ ^ 2 / (2 * canonicalScale N ^ 2)) := by
  change Complex.normSq ((gaussianAmplitude N *
    Real.exp (-‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2)) : ℝ) : ℂ) = _
  rw [Complex.normSq_ofReal]
  have he :
      -‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2) +
        -‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2) =
        -‖q - q₀‖ ^ 2 / (2 * canonicalScale N ^ 2) := by ring
  calc
    (gaussianAmplitude N * Real.exp (-‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2))) *
        (gaussianAmplitude N * Real.exp (-‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2))) =
        gaussianAmplitude N ^ 2 *
          (Real.exp (-‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2)) *
            Real.exp (-‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2))) := by ring
    _ = gaussianAmplitude N ^ 2 *
        Real.exp (-‖q - q₀‖ ^ 2 / (2 * canonicalScale N ^ 2)) := by
      rw [← Real.exp_add, he]

theorem gaussianAmplitude_sq (N : ℕ) :
    gaussianAmplitude N ^ 2 =
      (2 * Real.pi * canonicalScale N ^ 2) ^ (-(phaseDimension N : ℝ) / 2) := by
  have hbase : 0 ≤ 2 * Real.pi * canonicalScale N ^ 2 := by positivity
  unfold gaussianAmplitude
  calc
    ((2 * Real.pi * canonicalScale N ^ 2) ^ (-(phaseDimension N : ℝ) / 4)) ^ 2 =
        (2 * Real.pi * canonicalScale N ^ 2) ^
          ((-(phaseDimension N : ℝ) / 4) * (2 : ℝ)) :=
      (Real.rpow_mul_natCast hbase (-(phaseDimension N : ℝ) / 4) 2).symm
    _ = (2 * Real.pi * canonicalScale N ^ 2) ^ (-(phaseDimension N : ℝ) / 2) := by
      congr 1
      ring

theorem canonicalGaussian_integral (N : ℕ) (q₀ : Phase N) :
    (∫ q : Phase N, Real.exp (-‖q - q₀‖ ^ 2 / (2 * canonicalScale N ^ 2))) =
      (2 * Real.pi * canonicalScale N ^ 2) ^ ((phaseDimension N : ℝ) / 2) := by
  have hσ := canonicalScale_pos N
  have hb : 0 < (2 * canonicalScale N ^ 2)⁻¹ := by positivity
  calc
    (∫ q : Phase N, Real.exp (-‖q - q₀‖ ^ 2 / (2 * canonicalScale N ^ 2))) =
        ∫ q : Phase N, Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q - q₀‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with q
      congr 1
      ring
    _ = ∫ q : Phase N, Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q‖ ^ 2) :=
      integral_sub_right_eq_self _ q₀
    _ = (Real.pi / (2 * canonicalScale N ^ 2)⁻¹) ^
        ((Module.finrank ℝ (Phase N) : ℝ) / 2) :=
      GaussianFourier.integral_rexp_neg_mul_sq_norm hb
    _ = (2 * Real.pi * canonicalScale N ^ 2) ^ ((phaseDimension N : ℝ) / 2) := by
      simp only [phaseDimension, div_inv_eq_mul]
      congr 1
      ring

theorem canonicalPacket_normalized (N : ℕ) (q₀ : Phase N) :
    (∫ q, bornDensity (canonicalPacket N q₀) q ∂phaseVolume N) = 1 := by
  have hσ := canonicalScale_pos N
  have hbase : 0 < 2 * Real.pi * canonicalScale N ^ 2 := by positivity
  rw [phaseVolume_eq_volume]
  simp_rw [canonicalPacket_bornDensity]
  rw [integral_const_mul, canonicalGaussian_integral, gaussianAmplitude_sq,
    ← Real.rpow_add hbase]
  have he : -(phaseDimension N : ℝ) / 2 + (phaseDimension N : ℝ) / 2 = 0 := by ring
  rw [he, Real.rpow_zero]

theorem canonicalPacket_density_integrable (N : ℕ) (q₀ : Phase N) :
    Integrable (bornDensity (canonicalPacket N q₀)) (phaseVolume N) := by
  apply Integrable.of_integral_ne_zero
  rw [canonicalPacket_normalized]
  norm_num

theorem canonicalPacket_memLp (N : ℕ) (q₀ : Phase N) :
    MemLp (canonicalPacket N q₀) 2 (phaseVolume N) := by
  apply (memLp_two_iff_integrable_sq_norm
    (canonicalPacket_continuous N q₀).aestronglyMeasurable).2
  have hd : (fun q => ‖canonicalPacket N q₀ q‖ ^ 2) =
      bornDensity (canonicalPacket N q₀) := by
    funext q
    exact (Complex.normSq_eq_norm_sq (canonicalPacket N q₀ q)).symm
  rw [hd]
  exact canonicalPacket_density_integrable N q₀

theorem canonicalPacket_waveAdmissible (N : ℕ) (q₀ : Phase N) :
    WaveAdmissible (phaseVolume N) (canonicalPacket N q₀) :=
  ⟨canonicalPacket_memLp N q₀, canonicalPacket_normalized N q₀⟩

theorem canonicalPacket_norm_toL2 (N : ℕ) (q₀ : Phase N) :
    ‖(canonicalPacket_waveAdmissible N q₀).toL2‖ = 1 :=
  (canonicalPacket_waveAdmissible N q₀).norm_toL2

theorem phaseGaussian_moment_formula (N : ℕ) {b : ℝ} (hb : 0 < b) (k : ℕ) :
    (∫ q : Phase N, ‖q‖ ^ k * Real.exp (-b * ‖q‖ ^ 2)) =
      (phaseDimension N : ℝ) *
        (volume : Measure (Phase N)).real (Metric.ball 0 1) *
        (b ^ (-((phaseDimension N : ℝ) + k) / 2) * (1 / 2) *
          Real.Gamma (((phaseDimension N : ℝ) + k) / 2)) := by
  have hd : 0 < phaseDimension N := phase_finrank_pos N
  have hq : -1 < ((phaseDimension N - 1 + k : ℕ) : ℝ) := by
    have hn : 0 ≤ ((phaseDimension N - 1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hexp : ((phaseDimension N - 1 + k : ℕ) : ℝ) + 1 =
      (phaseDimension N : ℝ) + k := by
    exact_mod_cast (show phaseDimension N - 1 + k + 1 = phaseDimension N + k by omega)
  rw [integral_fun_norm_addHaar (volume : Measure (Phase N))
    (fun y : ℝ => y ^ k * Real.exp (-b * y ^ 2))]
  simp only [nsmul_eq_mul, smul_eq_mul]
  change (phaseDimension N : ℝ) *
    (volume : Measure (Phase N)).real (Metric.ball 0 1) *
    (∫ y in Set.Ioi (0 : ℝ), y ^ (phaseDimension N - 1) *
      (y ^ k * Real.exp (-b * y ^ 2))) = _
  have hfun :
      (fun y : ℝ => y ^ (phaseDimension N - 1) * (y ^ k * Real.exp (-b * y ^ 2))) =
      (fun y : ℝ => y ^ ((phaseDimension N - 1 + k : ℕ) : ℝ) *
        Real.exp (-b * y ^ (2 : ℝ))) := by
    funext y
    rw [Real.rpow_natCast, Real.rpow_two, pow_add]
    ring
  rw [hfun, integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2) hq hb,
    hexp]

theorem phaseGaussian_moment_integrable (N : ℕ) {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun q : Phase N => ‖q‖ ^ k * Real.exp (-b * ‖q‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure (Phase N))
    (f := fun y : ℝ => y ^ k * Real.exp (-b * y ^ 2))).2
  have hq : -1 < ((phaseDimension N - 1 + k : ℕ) : ℝ) := by
    have hn : 0 ≤ ((phaseDimension N - 1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hi := (integrable_rpow_mul_exp_neg_mul_sq hb hq).integrableOn
    (s := Set.Ioi (0 : ℝ))
  change IntegrableOn (fun y : ℝ => y ^ (phaseDimension N - 1) •
    (y ^ k * Real.exp (-b * y ^ 2))) (Set.Ioi 0)
  have hfun :
      (fun y : ℝ => y ^ (phaseDimension N - 1) • (y ^ k * Real.exp (-b * y ^ 2))) =
      (fun y : ℝ => y ^ ((phaseDimension N - 1 + k : ℕ) : ℝ) *
        Real.exp (-b * y ^ 2)) := by
    funext y
    rw [Real.rpow_natCast, pow_add, smul_eq_mul]
    ring
  rw [hfun]
  exact hi

theorem phaseGaussian_second_moment (N : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ q : Phase N, ‖q‖ ^ 2 * Real.exp (-b * ‖q‖ ^ 2)) =
      ((phaseDimension N : ℝ) / (2 * b)) *
        ∫ q : Phase N, Real.exp (-b * ‖q‖ ^ 2) := by
  have hd : 0 < (phaseDimension N : ℝ) := by exact_mod_cast phase_finrank_pos N
  have h0 := phaseGaussian_moment_formula N hb 0
  simp only [pow_zero, one_mul, Nat.cast_zero, add_zero] at h0
  have hp : b ^ (-((phaseDimension N : ℝ) + 2) / 2) =
      b ^ (-(phaseDimension N : ℝ) / 2) * b⁻¹ := by
    rw [show -((phaseDimension N : ℝ) + 2) / 2 =
      -(phaseDimension N : ℝ) / 2 + (-1) by ring,
      Real.rpow_add hb, Real.rpow_neg_one]
  have hg : Real.Gamma (((phaseDimension N : ℝ) + 2) / 2) =
      ((phaseDimension N : ℝ) / 2) * Real.Gamma ((phaseDimension N : ℝ) / 2) := by
    rw [show ((phaseDimension N : ℝ) + 2) / 2 =
      (phaseDimension N : ℝ) / 2 + 1 by ring,
      Real.Gamma_add_one (by positivity : (phaseDimension N : ℝ) / 2 ≠ 0)]
  rw [phaseGaussian_moment_formula N hb 2, h0]
  norm_num only [Nat.cast_ofNat]
  rw [hp, hg]
  ring

theorem phaseGaussian_fourth_moment (N : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ q : Phase N, ‖q‖ ^ 4 * Real.exp (-b * ‖q‖ ^ 2)) =
      ((phaseDimension N : ℝ) * ((phaseDimension N : ℝ) + 2) / (4 * b ^ 2)) *
        ∫ q : Phase N, Real.exp (-b * ‖q‖ ^ 2) := by
  have hd : 0 < (phaseDimension N : ℝ) := by exact_mod_cast phase_finrank_pos N
  have h0 := phaseGaussian_moment_formula N hb 0
  simp only [pow_zero, one_mul, Nat.cast_zero, add_zero] at h0
  have hp : b ^ (-((phaseDimension N : ℝ) + 4) / 2) =
      b ^ (-(phaseDimension N : ℝ) / 2) * (b ^ 2)⁻¹ := by
    rw [show -((phaseDimension N : ℝ) + 4) / 2 =
      -(phaseDimension N : ℝ) / 2 + (-(2 : ℝ)) by ring,
      Real.rpow_add hb, Real.rpow_neg hb.le, Real.rpow_two]
  have hg : Real.Gamma (((phaseDimension N : ℝ) + 4) / 2) =
      ((phaseDimension N : ℝ) / 2 + 1) * ((phaseDimension N : ℝ) / 2) *
        Real.Gamma ((phaseDimension N : ℝ) / 2) := by
    rw [show ((phaseDimension N : ℝ) + 4) / 2 =
      ((phaseDimension N : ℝ) / 2 + 1) + 1 by ring,
      Real.Gamma_add_one (by positivity : (phaseDimension N : ℝ) / 2 + 1 ≠ 0),
      Real.Gamma_add_one (by positivity : (phaseDimension N : ℝ) / 2 ≠ 0)]
    ring
  rw [phaseGaussian_moment_formula N hb 4, h0]
  norm_num only [Nat.cast_ofNat]
  rw [hp, hg]
  ring

theorem canonicalPacket_centered_integrand (N : ℕ) (q₀ q : Phase N) (k : ℕ) :
    ‖q - q₀‖ ^ k * bornDensity (canonicalPacket N q₀) q =
      gaussianAmplitude N ^ 2 * (‖q - q₀‖ ^ k *
        Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q - q₀‖ ^ 2)) := by
  rw [canonicalPacket_bornDensity]
  have he : -‖q - q₀‖ ^ 2 / (2 * canonicalScale N ^ 2) =
      -(2 * canonicalScale N ^ 2)⁻¹ * ‖q - q₀‖ ^ 2 := by ring
  rw [he]
  ring

theorem canonicalPacket_centered_moment (N : ℕ) (q₀ : Phase N) (k : ℕ) :
    (∫ q, ‖q - q₀‖ ^ k * bornDensity (canonicalPacket N q₀) q ∂phaseVolume N) =
      gaussianAmplitude N ^ 2 *
        ∫ q : Phase N, ‖q‖ ^ k * Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q‖ ^ 2) := by
  rw [phaseVolume_eq_volume]
  simp_rw [canonicalPacket_centered_integrand]
  rw [integral_const_mul, integral_sub_right_eq_self]

theorem canonicalPacket_centered_moment_integrable (N : ℕ) (q₀ : Phase N) (k : ℕ) :
    Integrable (fun q => ‖q - q₀‖ ^ k * bornDensity (canonicalPacket N q₀) q)
      (phaseVolume N) := by
  have hσ := canonicalScale_pos N
  have hb : 0 < (2 * canonicalScale N ^ 2)⁻¹ := by positivity
  have hi := ((phaseGaussian_moment_integrable N hb k).comp_sub_right q₀).const_mul
    (gaussianAmplitude N ^ 2)
  rw [phaseVolume_eq_volume]
  have hf : (fun q => ‖q - q₀‖ ^ k * bornDensity (canonicalPacket N q₀) q) =
      (fun q => gaussianAmplitude N ^ 2 * (‖q - q₀‖ ^ k *
        Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q - q₀‖ ^ 2))) := by
    funext q
    exact canonicalPacket_centered_integrand N q₀ q k
  rw [hf]
  exact hi

theorem canonicalPacket_second_moment (N : ℕ) (q₀ : Phase N) :
    (∫ q, ‖q - q₀‖ ^ 2 * bornDensity (canonicalPacket N q₀) q ∂phaseVolume N) =
      (phaseDimension N : ℝ) * canonicalScale N ^ 2 := by
  have hσ := canonicalScale_pos N
  have hb : 0 < (2 * canonicalScale N ^ 2)⁻¹ := by positivity
  have hnorm := canonicalPacket_centered_moment N q₀ 0
  simp only [pow_zero, one_mul] at hnorm
  rw [canonicalPacket_normalized] at hnorm
  rw [canonicalPacket_centered_moment, phaseGaussian_second_moment N hb]
  calc
    gaussianAmplitude N ^ 2 *
        (((phaseDimension N : ℝ) / (2 * (2 * canonicalScale N ^ 2)⁻¹)) *
          ∫ q : Phase N, Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q‖ ^ 2)) =
        ((phaseDimension N : ℝ) / (2 * (2 * canonicalScale N ^ 2)⁻¹)) *
          (gaussianAmplitude N ^ 2 *
            ∫ q : Phase N, Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q‖ ^ 2)) := by ring
    _ = (phaseDimension N : ℝ) / (2 * (2 * canonicalScale N ^ 2)⁻¹) := by
      rw [← hnorm, mul_one]
    _ = (phaseDimension N : ℝ) * canonicalScale N ^ 2 := by
      field_simp [ne_of_gt hσ]
      <;> ring

theorem canonicalPacket_fourth_moment (N : ℕ) (q₀ : Phase N) :
    (∫ q, ‖q - q₀‖ ^ 4 * bornDensity (canonicalPacket N q₀) q ∂phaseVolume N) =
      (phaseDimension N : ℝ) * ((phaseDimension N : ℝ) + 2) * canonicalScale N ^ 4 := by
  have hσ := canonicalScale_pos N
  have hb : 0 < (2 * canonicalScale N ^ 2)⁻¹ := by positivity
  have hnorm := canonicalPacket_centered_moment N q₀ 0
  simp only [pow_zero, one_mul] at hnorm
  rw [canonicalPacket_normalized] at hnorm
  rw [canonicalPacket_centered_moment, phaseGaussian_fourth_moment N hb]
  calc
    gaussianAmplitude N ^ 2 *
        (((phaseDimension N : ℝ) * ((phaseDimension N : ℝ) + 2) /
          (4 * ((2 * canonicalScale N ^ 2)⁻¹) ^ 2)) *
          ∫ q : Phase N, Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q‖ ^ 2)) =
        ((phaseDimension N : ℝ) * ((phaseDimension N : ℝ) + 2) /
          (4 * ((2 * canonicalScale N ^ 2)⁻¹) ^ 2)) *
          (gaussianAmplitude N ^ 2 *
            ∫ q : Phase N, Real.exp (-(2 * canonicalScale N ^ 2)⁻¹ * ‖q‖ ^ 2)) := by ring
    _ = (phaseDimension N : ℝ) * ((phaseDimension N : ℝ) + 2) /
        (4 * ((2 * canonicalScale N ^ 2)⁻¹) ^ 2) := by
      rw [← hnorm, mul_one]
    _ = (phaseDimension N : ℝ) * ((phaseDimension N : ℝ) + 2) * canonicalScale N ^ 4 := by
      field_simp [ne_of_gt hσ]
      <;> ring

end

end QuantumAdapter
