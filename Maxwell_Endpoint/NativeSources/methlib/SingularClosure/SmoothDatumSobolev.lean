import SingularClosure.FourierDecay
import SingularClosure.LatticeSobolevSummability

/-! Every smooth periodic physical datum has all integral-order Fourier Sobolev norms. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem finite_sum_pow_le_card_pow_mul_sum_pow {ι : Type*}
    (t : Finset ι) (ht : t.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ t, 0 ≤ f i) (n : ℕ) :
    (∑ i ∈ t, f i) ^ n ≤ (t.card : ℝ) ^ n * ∑ i ∈ t, f i ^ n := by
  obtain ⟨i, hi, hmax⟩ := t.exists_max_image f ht
  have hsum : (∑ j ∈ t, f j) ≤ (t.card : ℝ) * f i := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hmax
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg hf) hsum n
  rw [mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j hj => pow_nonneg (hf j hj) n) hi) (by positivity))

theorem torusSobolevWeight_pow_le_polynomial (n : ℕ) (k : Frequency) :
    torusSobolevWeight k ^ n ≤ (4 : ℝ) ^ n *
      (1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ (2 * n)) := by
  have hscale : (∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ 2) =
      laplacianFrequency k := by
    simpa only [mul_pow, sq_abs] using sum_derivativeScale_sq k
  have hsq : torusSobolevWeight k ^ 2 =
      1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ 2 := by
    rw [hscale]
    unfold torusSobolevWeight laplacianFrequency
    have hf : 0 ≤ (galerkinFreqSq k : ℝ) := by
      exact_mod_cast galerkinFreqSq_nonneg k
    exact Real.sq_sqrt (by positivity)
  let f : Fin 4 → ℝ := ![1, ((2 * Real.pi) * |(k 0 : ℝ)|) ^ 2,
    ((2 * Real.pi) * |(k 1 : ℝ)|) ^ 2, ((2 * Real.pi) * |(k 2 : ℝ)|) ^ 2]
  have hf (l : Fin 4) : 0 ≤ f l := by
    fin_cases l <;> simp [f] <;> positivity
  have hsum : (∑ l : Fin 4, f l) = torusSobolevWeight k ^ 2 := by
    rw [hsq]
    simp [f, Fin.sum_univ_succ] <;> ring
  have hsump : (∑ l : Fin 4, f l ^ n) =
      1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ (2 * n) := by
    simp [f, Fin.sum_univ_succ, ← pow_mul] <;> ring
  have hw : torusSobolevWeight k ≤ torusSobolevWeight k ^ 2 := by
    nlinarith [torusSobolevWeight_one_le k, sq_nonneg (torusSobolevWeight k - 1)]
  calc
    _ ≤ (torusSobolevWeight k ^ 2) ^ n :=
      pow_le_pow_left₀ (torusSobolevWeight_pos k).le hw n
    _ = (∑ l : Fin 4, f l) ^ n := by rw [hsum]
    _ ≤ (4 : ℝ) ^ n * ∑ l : Fin 4, f l ^ n := by
      simpa using finite_sum_pow_le_card_pow_mul_sum_pow Finset.univ
        Finset.univ_nonempty f (fun l _ => hf l) n
    _ = _ := by rw [hsump]

def smoothDatumDecayConstant (s : ℕ) (a : Field) : ℝ :=
  (4 : ℝ) ^ (s + 2) * fourierDecayConstant (2 * (s + 2)) a

theorem smoothDatumDecayConstant_nonneg (s : ℕ) (a : Field) :
    0 ≤ smoothDatumDecayConstant s a :=
  mul_nonneg (by positivity) (fourierDecayConstant_nonneg _ a)

theorem smooth_datum_sobolev_decay (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) (i : Fin 3) :
    torusSobolevWeight k ^ (s + 2) * ‖datumFourierCoeff a k i‖ ≤
      smoothDatumDecayConstant s a := by
  have hw := torusSobolevWeight_pow_le_polynomial (s + 2) k
  have hc := FOURIER_POLYNOMIAL_WEIGHT_BOUND (2 * (s + 2)) a ha hp k i
  calc
    _ ≤ ((4 : ℝ) ^ (s + 2) *
        (1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ (2 * (s + 2)))) *
        ‖datumFourierCoeff a k i‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = (4 : ℝ) ^ (s + 2) *
        ((1 + ∑ j : Fin 3, ((2 * Real.pi) * |(k j : ℝ)|) ^ (2 * (s + 2))) *
          ‖datumFourierCoeff a k i‖) := by ring
    _ ≤ smoothDatumDecayConstant s a :=
      mul_le_mul_of_nonneg_left hc (by positivity)

theorem smooth_datum_weightedCoeff_norm_le (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s (datumFourierCoeff a) ki‖ ≤
      smoothDatumDecayConstant s a * (torusSobolevWeight ki.1)⁻¹ ^ 2 := by
  have hw : 0 < torusSobolevWeight ki.1 ^ 2 := pow_pos (torusSobolevWeight_pos _) _
  have hb : ‖sobolevWeightedCoeff s (datumFourierCoeff a) ki‖ ≤
      smoothDatumDecayConstant s a / (torusSobolevWeight ki.1 ^ 2) := by
    apply (le_div_iff₀ hw).mpr
    calc
      _ = torusSobolevWeight ki.1 ^ (s + 2) * ‖datumFourierCoeff a ki.1 ki.2‖ := by
        simp only [sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos ki.1), pow_add]
        ring
      _ ≤ _ := smooth_datum_sobolev_decay s a ha hp ki.1 ki.2
  simpa only [div_eq_mul_inv, inv_pow] using hb

theorem smooth_datum_weightedCoeff_sq_le (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s (datumFourierCoeff a) ki‖ ^ 2 ≤
      smoothDatumDecayConstant s a ^ 2 * (torusSobolevWeight ki.1)⁻¹ ^ 4 := by
  calc
    _ ≤ (smoothDatumDecayConstant s a * (torusSobolevWeight ki.1)⁻¹ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (smooth_datum_weightedCoeff_norm_le s a ha hp ki) 2
    _ = _ := by ring

/-- Actual smooth periodic data belong to every integral-order Fourier Sobolev space. -/
theorem SMOOTH_DATUM_MEM_TORUS_SOBOLEV (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    Memℓp (sobolevWeightedCoeff s (datumFourierCoeff a)) 2 := by
  classical
  let C : ℝ := 3 * smoothDatumDecayConstant s a ^ 2 *
    ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4
  apply memℓp_gen' (C := C)
  intro t
  have hsub : t ⊆ (t.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  have hbound : (∑ ki ∈ t, ‖sobolevWeightedCoeff s (datumFourierCoeff a) ki‖ ^ 2) ≤ C := by
    calc
      _ ≤ ∑ ki ∈ t, smoothDatumDecayConstant s a ^ 2 *
          (torusSobolevWeight ki.1)⁻¹ ^ 4 :=
        Finset.sum_le_sum (fun ki _ => smooth_datum_weightedCoeff_sq_le s a ha hp ki)
      _ ≤ ∑ ki ∈ (t.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
          smoothDatumDecayConstant s a ^ 2 * (torusSobolevWeight ki.1)⁻¹ ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => by positivity)
      _ = 3 * smoothDatumDecayConstant s a ^ 2 *
          ∑ k ∈ t.image Prod.fst, (torusSobolevWeight k)⁻¹ ^ 4 := by
        simp [Finset.sum_product, Finset.mul_sum, mul_assoc]
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left
        · exact Summable.sum_le_tsum _ (fun k _ => by positivity)
            summable_torusSobolevWeight_inv_four
        · positivity
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hbound

/-- The initial Hilbert state is constructed from the physical integral coefficients. -/
def smoothDatumSobolev (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) : TorusSobolev s :=
  ⟨datumFourierCoeff a, SMOOTH_DATUM_MEM_TORUS_SOBOLEV s a ha hp⟩

theorem smoothDatumSobolev_coeff (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    (smoothDatumSobolev s a ha hp).val = datumFourierCoeff a := rfl

end

end SingularClosure
