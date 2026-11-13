import QuantumAdapter.Assembly.Gaussian
import QuantumAdapter.Assembly.Fourier
import QuantumAdapter.Assembly.Transport

/-!
Actual finite-cutoff packet admissibility. Gaussian moments control the
quadratic energy multiplier before transport; the native Jacobian formula
then transports both its L2 domain and its scalar expectation domain.
No packet-admissibility or moment certificate occurs among the premises.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory

namespace QuantumAdapter.Assembly

noncomputable section

theorem norm_pow_le_centered (N : ℕ) (q₀ q : Phase N) (k : ℕ) :
    ‖q‖ ^ k ≤ (2 : ℝ) ^ k * (‖q - q₀‖ ^ k + ‖q₀‖ ^ k) := by
  have hn : ‖q‖ ≤ ‖q - q₀‖ + ‖q₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q - q₀) q₀
  rcases le_total ‖q - q₀‖ ‖q₀‖ with h | h
  · have hn' : ‖q‖ ≤ 2 * ‖q₀‖ := by linarith
    calc
      ‖q‖ ^ k ≤ (2 * ‖q₀‖) ^ k := pow_le_pow_left₀ (norm_nonneg q) hn' k
      _ = (2 : ℝ) ^ k * ‖q₀‖ ^ k := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ k * (‖q - q₀‖ ^ k + ‖q₀‖ ^ k) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _))
          (pow_nonneg (by norm_num) _)
  · have hn' : ‖q‖ ≤ 2 * ‖q - q₀‖ := by linarith
    calc
      ‖q‖ ^ k ≤ (2 * ‖q - q₀‖) ^ k := pow_le_pow_left₀ (norm_nonneg q) hn' k
      _ = (2 : ℝ) ^ k * ‖q - q₀‖ ^ k := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ k * (‖q - q₀‖ ^ k + ‖q₀‖ ^ k) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _))
          (pow_nonneg (by norm_num) _)

theorem canonicalPacket_bornDensity_continuous (N : ℕ) (q₀ : Phase N) :
    Continuous (bornDensity (canonicalPacket N q₀)) :=
  Complex.continuous_normSq.comp (canonicalPacket_continuous N q₀)

theorem canonicalPacket_raw_moment_integrable (N : ℕ) (q₀ : Phase N) (k : ℕ) :
    Integrable (fun q => ‖q‖ ^ k * bornDensity (canonicalPacket N q₀) q)
      (phaseVolume N) := by
  have hi := ((canonicalPacket_centered_moment_integrable N q₀ k).add
    ((canonicalPacket_density_integrable N q₀).const_mul (‖q₀‖ ^ k))).const_mul
      ((2 : ℝ) ^ k)
  apply hi.mono'
  · exact ((continuous_norm.pow k).mul
      (canonicalPacket_bornDensity_continuous N q₀)).aestronglyMeasurable
  · filter_upwards [] with q
    change ‖‖q‖ ^ k * bornDensity (canonicalPacket N q₀) q‖ ≤
      (2 : ℝ) ^ k * (‖q - q₀‖ ^ k * bornDensity (canonicalPacket N q₀) q +
        ‖q₀‖ ^ k * bornDensity (canonicalPacket N q₀) q)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (bornDensity_nonneg _ _))]
    calc
      ‖q‖ ^ k * bornDensity (canonicalPacket N q₀) q ≤
          ((2 : ℝ) ^ k * (‖q - q₀‖ ^ k + ‖q₀‖ ^ k)) *
            bornDensity (canonicalPacket N q₀) q :=
        mul_le_mul_of_nonneg_right (norm_pow_le_centered N q₀ q k)
          (bornDensity_nonneg _ _)
      _ = _ := by ring

theorem canonicalPacket_observableIntegrable_of_quadratic_bound
    (N : ℕ) (q₀ : Phase N) {f : Phase N → ℝ} (hf : Continuous f)
    (hf0 : ∀ q, 0 ≤ f q) {C : ℝ}
    (hbound : ∀ q, f q ≤ C * ‖q‖ ^ 2) :
    ObservableIntegrable (phaseVolume N) f (canonicalPacket N q₀) := by
  have hi := (canonicalPacket_raw_moment_integrable N q₀ 2).const_mul C
  apply hi.mono'
  · exact (hf.mul (canonicalPacket_bornDensity_continuous N q₀)).aestronglyMeasurable
  · filter_upwards [] with q
    change ‖f q * bornDensity (canonicalPacket N q₀) q‖ ≤
      C * (‖q‖ ^ 2 * bornDensity (canonicalPacket N q₀) q)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 q) (bornDensity_nonneg _ _))]
    exact (mul_le_mul_of_nonneg_right (hbound q) (bornDensity_nonneg _ _)).trans_eq
      (mul_assoc _ _ _)

theorem canonicalPacket_multiplierDomain_of_quadratic_bound
    (N : ℕ) (q₀ : Phase N) {f : Phase N → ℝ} (hf : Continuous f)
    (hf0 : ∀ q, 0 ≤ f q) {C : ℝ}
    (hbound : ∀ q, f q ≤ C * ‖q‖ ^ 2) :
    MultiplierDomain (phaseVolume N) f (canonicalPacket N q₀) := by
  refine ⟨canonicalPacket_memLp N q₀, ?_⟩
  have hprod : Continuous (fun q => (f q : ℂ) * canonicalPacket N q₀ q) :=
    (Complex.continuous_ofReal.comp hf).mul (canonicalPacket_continuous N q₀)
  apply (memLp_two_iff_integrable_sq_norm hprod.aestronglyMeasurable).2
  have hi := (canonicalPacket_raw_moment_integrable N q₀ 4).const_mul (C ^ 2)
  apply hi.mono'
  · exact (hprod.norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with q
    have hs : f q ^ 2 ≤ C ^ 2 * ‖q‖ ^ 4 := by
      calc
        f q ^ 2 ≤ (C * ‖q‖ ^ 2) ^ 2 := pow_le_pow_left₀ (hf0 q) (hbound q) 2
        _ = C ^ 2 * ‖q‖ ^ 4 := by ring
    change ‖‖(f q : ℂ) * canonicalPacket N q₀ q‖ ^ 2‖ ≤
      C ^ 2 * (‖q‖ ^ 4 * bornDensity (canonicalPacket N q₀) q)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
    change (f q * f q) * bornDensity (canonicalPacket N q₀) q ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hs (bornDensity_nonneg (canonicalPacket N q₀) q)]

theorem phaseFlow_energy3_le_quadratic {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) (q : Phase N) :
    energy3 N (F.map N t q) ≤ cutoffSobolevFactor N ^ 2 * ‖q‖ ^ 2 := by
  have he := (phaseFlow_isTrajectory F N q).energy0_le_initial hν ht
  rw [energy0_eq_norm_sq, energy0_eq_norm_sq] at he
  exact (energy3_le_cutoffSobolevFactor_sq_mul_norm_sq N (F.map N t q)).trans
    (mul_le_mul_of_nonneg_left he (sq_nonneg _))

theorem transportedPacket_quantumAdmissible_of_jacobian {ν : ℝ}
    (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (N : ℕ) (q₀ : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    quantumAdmissible F N q₀ t := by
  let L := phaseTransportLaws_of_jacobian F hd hdet
  have hw : WaveAdmissible (phaseVolume N) (transportedPacket F N q₀ t) :=
    transport_waveAdmissible F L N t (canonicalPacket_waveAdmissible N q₀)
  let f : Phase N → ℝ := fun q => energy3 N (F.map N t q)
  have hf : Continuous f := (continuous_energy3 N).comp (hd N t).continuous
  have hf0 : ∀ q, 0 ≤ f q := fun q => energy3_nonneg N (F.map N t q)
  have hbound : ∀ q, f q ≤ cutoffSobolevFactor N ^ 2 * ‖q‖ ^ 2 :=
    phaseFlow_energy3_le_quadratic hν F N t ht
  have hmult := canonicalPacket_multiplierDomain_of_quadratic_bound N q₀ hf hf0 hbound
  have hobs := canonicalPacket_observableIntegrable_of_quadratic_bound N q₀ hf hf0 hbound
  have hinv (q : Phase N) : F.map N t (F.map N (-t) q) = q := by
    rw [← F.map_add, add_neg_cancel, F.map_zero]
  refine ⟨hw, ⟨hw.memLp, ?_⟩, ?_⟩
  · have hp := (L.memLp_law N) t
      (fun q => (f q : ℂ) * canonicalPacket N q₀ q) hmult.product_memLp
    have heq :
        halfDensityPullback (phaseDecayRate ν N) (F.map N) t
          (fun q => (f q : ℂ) * canonicalPacket N q₀ q) =
        (fun q => (energy3 N q : ℂ) * transportedPacket F N q₀ t q) := by
      funext q
      dsimp [f, halfDensityPullback, transportedPacket, transport]
      rw [hinv]
      ring
    rw [heq] at hp
    exact hp
  · have hi := phaseFlow_integrable_weighted_comp_of_jacobian F hd hdet N t
      (fun q => f q * bornDensity (canonicalPacket N q₀) q) hobs
    change Integrable (fun q => energy3 N q *
      bornDensity (transportedPacket F N q₀ t) q) (phaseVolume N)
    apply hi.congr
    filter_upwards [] with q
    change Real.exp (phaseDecayRate ν N * t) *
      (f (F.map N (-t) q) * bornDensity (canonicalPacket N q₀) (F.map N (-t) q)) =
      energy3 N q * bornDensity
        (halfDensityPullback (phaseDecayRate ν N) (F.map N) t (canonicalPacket N q₀)) q
    rw [bornDensity_halfDensityPullback]
    dsimp [f]
    rw [hinv]
    ring

end

end QuantumAdapter.Assembly
