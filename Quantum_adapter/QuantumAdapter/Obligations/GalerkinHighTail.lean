import QuantumAdapter.Obligations.GalerkinResidualNorm
import QuantumAdapter.Obligations.GalerkinReferenceBounds
import SingularClosure.LatticeSobolevSummability

/-!
# Quantitative high-order cutoff tails of the actual smooth reference

The native H0 cutoff error gains any prescribed power of the cutoff from the
corresponding actual Sobolev norm. A coarse polynomial count of retained
frequencies is sufficient for the consistency estimate.
-/
set_option autoImplicit false
set_option Elab.async true
open Set Filter
open scoped BigOperators Topology ENNReal ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (NSSolution Data SmoothVelocity)

theorem torusSobolev_norm_sq_eq_tsum_density (s : ℕ) (c : TorusSobolev s) :
    ‖c‖ ^ 2 = ∑' k : Frequency, sobolevEnergyDensity s c.val k := by
  have hs : Summable (fun ki : FourierIndex => ‖sobolevWeightedCoeff s c.val ki‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      c.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  rw [torusSobolev_norm_sq]
  simp only [← sobolevWeightedCoeff_norm_eq]
  rw [hs.tsum_prod]
  simp only [tsum_fintype, sobolevEnergyDensity]

/-- The full smooth coefficient norm has the same explicit majorant as its finite cutoffs. -/
theorem smoothDatumSobolev_norm_sq_le (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    ‖(⟨datumFourierCoeff a, SMOOTH_DATUM_MEM_TORUS_SOBOLEV s a ha hp⟩ : TorusSobolev s)‖ ^ 2 ≤
      initialSobolevMajorant s a := by
  rw [torusSobolev_norm_sq_eq_tsum_density]
  calc
    _ ≤ ∑' k : Frequency, 3 * smoothDatumDecayConstant s a ^ 2 *
        (torusSobolevWeight k)⁻¹ ^ 4 :=
      tsum_le_tsum (fun k => initialSobolevEnergyDensity_le s a ha hp k)
        (smooth_datum_sobolevEnergyDensity_summable s a ha hp)
        (summable_torusSobolevWeight_inv_four.mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- High-order quantitative tail in the actual H0 norm, without zero-mean restriction. -/
theorem torusSobolev_cutoff_high_tail (m N : ℕ) (hN : 0 < N)
    (c : TorusSobolev 0) (d : TorusSobolev m) (hcd : c.val = d.val) :
    ‖torusSobolevCutoff 0 N c - c‖ ≤ ((N : ℝ)⁻¹) ^ m * ‖d‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNp : 0 ≤ ((N : ℝ)⁻¹) ^ m := pow_nonneg (inv_nonneg.mpr hNr.le) _
  rw [norm_sub_rev]
  calc
    _ ≤ ‖((N : ℝ)⁻¹) ^ m • torusSobolevRepr m d‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      change ‖(torusSobolevWeight ki.1 : ℂ) ^ 0 *
          (c.val ki.1 ki.2 - (torusSobolevCutoff 0 N c).val ki.1 ki.2)‖ ≤
        ‖((N : ℝ)⁻¹) ^ m • sobolevWeightedCoeff m d.val ki‖
      rw [torusSobolevCutoff_coeff]
      by_cases hk : ki.1 ∈ sobolevCutoffModes N
      · rw [if_pos hk, sub_self, mul_zero, norm_zero]
        exact norm_nonneg _
      · rw [if_neg hk, sub_zero, pow_zero, one_mul, hcd,
          norm_smul, Real.norm_of_nonneg hNp, sobolevWeightedCoeff_norm_eq]
        have hbase : 1 ≤ (N : ℝ)⁻¹ * torusSobolevWeight ki.1 := by
          calc
            1 = (N : ℝ)⁻¹ * (N : ℝ) := (inv_mul_cancel₀ hNr.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left (torusSobolevWeight_ge_cutoff hk)
              (inv_nonneg.mpr hNr.le)
        have hp : 1 ≤ ((N : ℝ)⁻¹) ^ m * torusSobolevWeight ki.1 ^ m := by
          simpa only [one_pow, mul_pow] using pow_le_pow_left₀ zero_le_one hbase m
        calc
          _ = 1 * ‖d.val ki.1 ki.2‖ := (one_mul _).symm
          _ ≤ (((N : ℝ)⁻¹) ^ m * torusSobolevWeight ki.1 ^ m) * ‖d.val ki.1 ki.2‖ :=
            mul_le_mul_of_nonneg_right hp (norm_nonneg _)
          _ = _ := by ring
    _ = _ := by
      rw [norm_smul, Real.norm_of_nonneg hNp, (torusSobolevRepr m).norm_map]

/-- A retained frequency has at most polynomial weight in the cutoff. -/
theorem retained_weight_sq_le (N : ℕ) (hN : 1 ≤ N) (k : Frequency)
    (hk : k ∈ fullModes N) :
    torusSobolevWeight k ^ 2 ≤ (1 + 4 * Real.pi ^ 2) * (N : ℝ) ^ 2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hl := laplaceSymbol_le_cutoffLambda N k hk
  rw [torusSobolevWeight_sq_native]
  unfold cutoffLambda at hl
  nlinarith

/-- A summable inverse-weight majorant replaces a separate lattice-point counting theorem. -/
theorem retained_weight_tenth_sum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ fullModes N, torusSobolevWeight k ^ 10) ≤
      (1 + 4 * Real.pi ^ 2) ^ 7 * (N : ℝ) ^ 14 * latticeSobolevConstant := by
  have hpoint (k : Frequency) (hk : k ∈ fullModes N) :
      torusSobolevWeight k ^ 10 ≤
        ((1 + 4 * Real.pi ^ 2) ^ 7 * (N : ℝ) ^ 14) *
          (torusSobolevWeight k)⁻¹ ^ 4 := by
    have hpow := pow_le_pow_left₀ (sq_nonneg (torusSobolevWeight k))
      (retained_weight_sq_le N hN k hk) 7
    have h14 : torusSobolevWeight k ^ 14 ≤
        (1 + 4 * Real.pi ^ 2) ^ 7 * (N : ℝ) ^ 14 := by
      simpa only [mul_pow, ← pow_mul] using hpow
    have hcancel : torusSobolevWeight k ^ 14 * (torusSobolevWeight k)⁻¹ ^ 4 =
        torusSobolevWeight k ^ 10 := by
      field_simp [(torusSobolevWeight_pos k).ne']
      ring
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_right h14 (by positivity)
  have hs : (∑ k ∈ fullModes N, (torusSobolevWeight k)⁻¹ ^ 4) ≤ latticeSobolevConstant := by
    have h := Summable.sum_le_tsum (fullModes N) (fun k hk => by positivity)
      summable_torusSobolevWeight_inv_four
    unfold latticeSobolevConstant
    linarith
  calc
    _ ≤ ∑ k ∈ fullModes N,
        ((1 + 4 * Real.pi ^ 2) ^ 7 * (N : ℝ) ^ 14) *
          (torusSobolevWeight k)⁻¹ ^ 4 := Finset.sum_le_sum (fun k hk => hpoint k hk)
    _ = _ := by rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- Joint smoothness supplies actual full coefficient norms uniformly on every finite horizon. -/
theorem NSSolution.exists_uniform_referenceSobolev_norm_sq
    (h : NSSolution ν a u p) (m : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ ht : 0 ≤ t, t ≤ T →
      ‖referenceSobolevAt h m t ht‖ ^ 2 ≤ C := by
  obtain ⟨C, hC, hb⟩ := h.exists_uniform_smoothDatumDecayConstant m T
  let W : ℝ := ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨3 * C ^ 2 * W, by positivity, ?_⟩
  intro t ht htT
  have hnorm := smoothDatumSobolev_norm_sq_le m (u t)
    (h.spatial_data t ht).smooth (h.spatial_data t ht).periodic
  apply hnorm.trans
  apply mul_le_mul_of_nonneg_right _ hW
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  exact pow_le_pow_left₀ (smoothDatumDecayConstant_nonneg m (u t)) (hb t ht htT) 2

/-- The literal projected reference has a uniform H0 tail gaining eight derivatives. -/
theorem reference_h0_tail_sq_le_h8 (h : NSSolution ν a u p)
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    ‖phaseSobolev 0 N (referenceProjection h N t) - referenceSobolevAt h 0 t ht‖ ^ 2 ≤
      ((N : ℝ)⁻¹) ^ 16 * ‖referenceSobolevAt h 8 t ht‖ ^ 2 := by
  rw [reference_phaseSobolev_eq_cutoff]
  have htail := torusSobolev_cutoff_high_tail 8 N hN
    (referenceSobolevAt h 0 t ht) (referenceSobolevAt h 8 t ht) rfl
  have hs := pow_le_pow_left₀ (norm_nonneg _) htail 2
  simpa only [mul_pow, ← pow_mul] using hs

end
end QuantumAdapter.Obligations
