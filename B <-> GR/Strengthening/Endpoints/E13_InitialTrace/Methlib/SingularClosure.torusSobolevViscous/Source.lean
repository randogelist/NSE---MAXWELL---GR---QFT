import SingularClosure.TorusGalerkinSobolev
import SingularClosure.LerayL2Contraction

/-! Concrete continuous linear operations on the weighted Fourier Sobolev spaces. -/

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal

namespace SingularClosure

noncomputable section

theorem torusSobolev_weightedCoeff_norm (s : ℕ) (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s c ki‖ =
      torusSobolevWeight ki.1 ^ s * ‖c ki.1 ki.2‖ := by
  simp only [sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos ki.1)]

theorem torusSobolev_weightedCoeff_norm_mono {s t : ℕ} (hst : s ≤ t)
    (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s c ki‖ ≤ ‖sobolevWeightedCoeff t c ki‖ := by
  rw [torusSobolev_weightedCoeff_norm, torusSobolev_weightedCoeff_norm]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (torusSobolevWeight_one_le ki.1) hst) (norm_nonneg _)

/-- A concrete lift of a coefficient operator, with an opaque membership proof. -/
theorem exists_torusSobolevLiftValue (s t : ℕ)
    (f : FourierCoeff →ₗ[ℂ] FourierCoeff)
    (hf : ∀ c : TorusSobolev t, Memℓp (sobolevWeightedCoeff s (f c.val)) 2)
    (c : TorusSobolev t) : ∃ v : TorusSobolev s, v.val = f c.val :=
  ⟨⟨f c.val, hf c⟩, Eq.refl (f c.val)⟩

def torusSobolevLiftValue (s t : ℕ) (f : FourierCoeff →ₗ[ℂ] FourierCoeff)
    (hf : ∀ c : TorusSobolev t, Memℓp (sobolevWeightedCoeff s (f c.val)) 2)
    (c : TorusSobolev t) : TorusSobolev s :=
  (exists_torusSobolevLiftValue s t f hf c).choose

@[simp]
theorem torusSobolevLiftValue_coeff (s t : ℕ) (f : FourierCoeff →ₗ[ℂ] FourierCoeff)
    (hf : ∀ c : TorusSobolev t, Memℓp (sobolevWeightedCoeff s (f c.val)) 2)
    (c : TorusSobolev t) : (torusSobolevLiftValue s t f hf c).val = f c.val :=
  (exists_torusSobolevLiftValue s t f hf c).choose_spec

def torusSobolevLiftLinear (s t : ℕ) (f : FourierCoeff →ₗ[ℂ] FourierCoeff)
    (hf : ∀ c : TorusSobolev t, Memℓp (sobolevWeightedCoeff s (f c.val)) 2) :
    TorusSobolev t →ₗ[ℂ] TorusSobolev s where
  toFun := torusSobolevLiftValue s t f hf
  map_add' c d := by
    apply Subtype.ext
    change (torusSobolevLiftValue s t f hf (c + d)).val =
      (torusSobolevLiftValue s t f hf c).val + (torusSobolevLiftValue s t f hf d).val
    rw [torusSobolevLiftValue_coeff, torusSobolevLiftValue_coeff,
      torusSobolevLiftValue_coeff]
    exact map_add f c.val d.val
  map_smul' z c := by
    apply Subtype.ext
    change (torusSobolevLiftValue s t f hf (z • c)).val =
      z • (torusSobolevLiftValue s t f hf c).val
    rw [torusSobolevLiftValue_coeff, torusSobolevLiftValue_coeff]
    exact map_smul f z c.val

@[simp]
theorem torusSobolevLiftLinear_coeff (s t : ℕ) (f : FourierCoeff →ₗ[ℂ] FourierCoeff)
    (hf : ∀ c : TorusSobolev t, Memℓp (sobolevWeightedCoeff s (f c.val)) 2)
    (c : TorusSobolev t) : (torusSobolevLiftLinear s t f hf c).val = f c.val :=
  torusSobolevLiftValue_coeff s t f hf c

theorem torusSobolevLower_mem (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    Memℓp (sobolevWeightedCoeff s c.val) 2 :=
  c.property.mono' (torusSobolev_weightedCoeff_norm_mono hst c.val)

def torusSobolevLowerLinear (s t : ℕ) (hst : s ≤ t) :
    TorusSobolev t →ₗ[ℂ] TorusSobolev s :=
  torusSobolevLiftLinear s t LinearMap.id (torusSobolevLower_mem s t hst)

@[simp]
theorem torusSobolevLowerLinear_coeff (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    (torusSobolevLowerLinear s t hst c).val = c.val :=
  torusSobolevLiftLinear_coeff s t LinearMap.id (torusSobolevLower_mem s t hst) c

theorem torusSobolevLowerLinear_norm_le (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    ‖torusSobolevLowerLinear s t hst c‖ ≤ ‖c‖ := by
  calc
    _ = ‖torusSobolevRepr s (torusSobolevLowerLinear s t hst c)‖ :=
      ((torusSobolevRepr s).norm_map _).symm
    _ ≤ ‖torusSobolevRepr t c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [torusSobolevRepr_apply, torusSobolevLowerLinear_coeff]
      exact torusSobolev_weightedCoeff_norm_mono hst c.val ki
    _ = ‖c‖ := (torusSobolevRepr t).norm_map c

theorem torusSobolevLower_bound (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    ‖torusSobolevLowerLinear s t hst c‖ ≤ 1 * ‖c‖ := by
  simpa only [one_mul] using torusSobolevLowerLinear_norm_le s t hst c

def torusSobolevLower (s t : ℕ) (hst : s ≤ t) : TorusSobolev t →L[ℂ] TorusSobolev s :=
  (torusSobolevLowerLinear s t hst).mkContinuous 1 (torusSobolevLower_bound s t hst)

@[simp]
theorem torusSobolevLower_coeff (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    (torusSobolevLower s t hst c).val = c.val := by
  unfold torusSobolevLower
  exact (congrArg (fun v : TorusSobolev s => v.val)
    ((torusSobolevLowerLinear s t hst).mkContinuous_apply 1
      (torusSobolevLower_bound s t hst) c)).trans (torusSobolevLowerLinear_coeff s t hst c)

theorem torusSobolevLower_coeff_apply (s t : ℕ) (hst : s ≤ t)
    (c : TorusSobolev t) (k : Frequency) (i : Fin 3) :
    (torusSobolevLower s t hst c).val k i = c.val k i :=
  congrArg (fun v : FourierCoeff => v k i) (torusSobolevLower_coeff s t hst c)

theorem torusSobolevLower_norm_le (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    ‖torusSobolevLower s t hst c‖ ≤ ‖c‖ :=
  torusSobolevLowerLinear_norm_le s t hst c

theorem torusSobolev_finite_weighted_sum_le (s : ℕ) (c : TorusSobolev s)
    (S : Finset FourierIndex) :
    (∑ ki ∈ S, ‖sobolevWeightedCoeff s c.val ki‖ ^ 2) ≤ ‖c‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
    (torusSobolevRepr s c) S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    torusSobolevRepr_apply, sobolevWeightedCoeff, (torusSobolevRepr s).norm_map] using h

theorem torusSobolev_multiplier_weighted_norm_le (s t : ℕ)
    (b : Frequency → ℂ) (B : ℝ)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s (fun k i => b k * c k i) ki‖ ≤
      B * ‖sobolevWeightedCoeff t c ki‖ := by
  rw [torusSobolev_weightedCoeff_norm, torusSobolev_weightedCoeff_norm, norm_mul]
  calc
    _ = (torusSobolevWeight ki.1 ^ s * ‖b ki.1‖) * ‖c ki.1 ki.2‖ := by ring
    _ ≤ (B * torusSobolevWeight ki.1 ^ t) * ‖c ki.1 ki.2‖ :=
      mul_le_mul_of_nonneg_right (hb ki.1) (norm_nonneg _)
    _ = _ := by ring

def fourierMultiplierLinear (b : Frequency → ℂ) : FourierCoeff →ₗ[ℂ] FourierCoeff where
  toFun c := fun k i => b k * c k i
  map_add' c d := by
    funext k i
    exact mul_add _ _ _
  map_smul' z c := by
    funext k i
    exact mul_left_comm _ _ _

theorem torusSobolevMultiplier_mem (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    Memℓp (sobolevWeightedCoeff s (fourierMultiplierLinear b c.val)) 2 := by
  apply (c.property.const_smul (B : ℂ)).mono'
  intro ki
  change ‖sobolevWeightedCoeff s (fun k i => b k * c.val k i) ki‖ ≤
    ‖(B : ℂ) * sobolevWeightedCoeff t c.val ki‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
  exact torusSobolev_multiplier_weighted_norm_le s t b B hb c.val ki

def torusSobolevMultiplierLinear (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t) :
    TorusSobolev t →ₗ[ℂ] TorusSobolev s :=
  torusSobolevLiftLinear s t (fourierMultiplierLinear b)
    (torusSobolevMultiplier_mem s t b B hB hb)

@[simp]
theorem torusSobolevMultiplierLinear_coeff (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    (torusSobolevMultiplierLinear s t b B hB hb c).val = fun k i => b k * c.val k i :=
  torusSobolevLiftLinear_coeff s t (fourierMultiplierLinear b)
    (torusSobolevMultiplier_mem s t b B hB hb) c

theorem torusSobolevMultiplierLinear_norm_le (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    ‖torusSobolevMultiplierLinear s t b B hB hb c‖ ≤ B * ‖c‖ := by
  calc
    _ = ‖torusSobolevRepr s (torusSobolevMultiplierLinear s t b B hB hb c)‖ :=
      ((torusSobolevRepr s).norm_map _).symm
    _ ≤ ‖(B : ℂ) • torusSobolevRepr t c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [torusSobolevRepr_apply, torusSobolevMultiplierLinear_coeff]
      change ‖sobolevWeightedCoeff s (fun k i => b k * c.val k i) ki‖ ≤
        ‖(B : ℂ) * sobolevWeightedCoeff t c.val ki‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
      exact torusSobolev_multiplier_weighted_norm_le s t b B hb c.val ki
    _ = _ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB,
        (torusSobolevRepr t).norm_map]

def torusSobolevMultiplier (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t) :
    TorusSobolev t →L[ℂ] TorusSobolev s :=
  (torusSobolevMultiplierLinear s t b B hB hb).mkContinuous B
    (torusSobolevMultiplierLinear_norm_le s t b B hB hb)

@[simp]
theorem torusSobolevMultiplier_coeff (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    (torusSobolevMultiplier s t b B hB hb c).val = fun k i => b k * c.val k i := by
  unfold torusSobolevMultiplier
  exact (congrArg (fun v : TorusSobolev s => v.val)
    ((torusSobolevMultiplierLinear s t b B hB hb).mkContinuous_apply B
      (torusSobolevMultiplierLinear_norm_le s t b B hB hb) c)).trans
    (torusSobolevMultiplierLinear_coeff s t b B hB hb c)

theorem torusSobolev_laplacian_multiplier_bound (s : ℕ) (k : Frequency) :
    torusSobolevWeight k ^ s * ‖-(laplacianFrequency k : ℂ)‖ ≤
      1 * torusSobolevWeight k ^ (s + 2) := by
  have hfreq : 0 ≤ laplacianFrequency k := by
    unfold laplacianFrequency
    have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
      exact_mod_cast galerkinFreqSq_nonneg k
    positivity
  have hweight : laplacianFrequency k ≤ torusSobolevWeight k ^ 2 := by
    rw [torusSobolevWeight_sq]
    unfold laplacianFrequency
    linarith
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfreq,
    one_mul, pow_add]
  exact mul_le_mul_of_nonneg_left hweight (pow_nonneg (torusSobolevWeight_pos k).le s)

def torusSobolevLaplacian (s : ℕ) : TorusSobolev (s + 2) →L[ℂ] TorusSobolev s :=
  torusSobolevMultiplier s (s + 2) (fun k => -(laplacianFrequency k : ℂ))
    1 zero_le_one (torusSobolev_laplacian_multiplier_bound s)

@[simp]
theorem torusSobolevLaplacian_coeff (s : ℕ) (c : TorusSobolev (s + 2)) :
    (torusSobolevLaplacian s c).val = fun k i => -(laplacianFrequency k : ℂ) * c.val k i :=
  torusSobolevMultiplier_coeff s (s + 2) (fun k => -(laplacianFrequency k : ℂ))
    1 zero_le_one (torusSobolev_laplacian_multiplier_bound s) c

def torusSobolevViscous (ν : ℝ) (s : ℕ) : TorusSobolev (s + 2) →L[ℂ] TorusSobolev s :=
  (ν : ℂ) • torusSobolevLaplacian s

@[simp]
theorem torusSobolevViscous_coeff (ν : ℝ) (s : ℕ) (c : TorusSobolev (s + 2)) :
    (torusSobolevViscous ν s c).val = fun k i =>
      -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c.val k i := by
  change ((ν : ℂ) • (torusSobolevLaplacian s c)).val = _
  change (ν : ℂ) • (torusSobolevLaplacian s c).val = _
  rw [torusSobolevLaplacian_coeff]
  funext k i
  simp only [Pi.smul_apply, smul_eq_mul, laplacianFrequency, Complex.ofReal_mul]
  ring

theorem coefficientLeray_add_arg (k : Frequency) (v w : Fin 3 → ℂ) :
    coefficientLeray k (v + w) = coefficientLeray k v + coefficientLeray k w := by
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, if_neg hk, Pi.add_apply, mul_add,
      Finset.sum_add_distrib, add_div]
    ring

theorem coefficientLeray_smul_arg (k : Frequency) (z : ℂ) (v : Fin 3 → ℂ) :
    coefficientLeray k (z • v) = z • coefficientLeray k v := by
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · have hsum : (∑ j : Fin 3, (k j : ℂ) * (z * v j)) =
        z * ∑ j : Fin 3, (k j : ℂ) * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [coefficientLeray, if_neg hk, Pi.smul_apply, smul_eq_mul, hsum]
    ring

theorem torusSobolev_leray_mode_sum_le (s : ℕ) (c : FourierCoeff) (k : Frequency) :
    (∑ i : Fin 3, ‖sobolevWeightedCoeff s (lerayFourierCoeff c) (k, i)‖ ^ 2) ≤
      ∑ i : Fin 3, ‖sobolevWeightedCoeff s c (k, i)‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (coefficientLeray_energy_le k (c k))
    (sq_nonneg (torusSobolevWeight k ^ s))
  simpa only [torusSobolev_weightedCoeff_norm, lerayFourierCoeff,
    Complex.normSq_eq_norm_sq, Finset.mul_sum, mul_pow] using h

theorem torusSobolev_leray_finite_sum_le (s : ℕ) (c : TorusSobolev s)
    (S : Finset FourierIndex) :
    (∑ ki ∈ S, ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) ki‖ ^ 2) ≤ ‖c‖ ^ 2 := by
  classical
  have hsub : S ⊆ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) ki‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => sq_nonneg _)
    _ = ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) (k, i)‖ ^ 2 :=
      Finset.sum_product (S.image Prod.fst) Finset.univ
        (fun ki : FourierIndex => ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) ki‖ ^ 2)
    _ ≤ ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s c.val (k, i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k hk => torusSobolev_leray_mode_sum_le s c.val k)
    _ = ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff s c.val ki‖ ^ 2 :=
      (Finset.sum_product (S.image Prod.fst) Finset.univ
        (fun ki : FourierIndex => ‖sobolevWeightedCoeff s c.val ki‖ ^ 2)).symm
    _ ≤ ‖c‖ ^ 2 := torusSobolev_finite_weighted_sum_le s c _

def fourierLerayLinear : FourierCoeff →ₗ[ℂ] FourierCoeff where
  toFun := lerayFourierCoeff
  map_add' c d := by
    funext k
    exact coefficientLeray_add_arg k (c k) (d k)
  map_smul' z c := by
    funext k
    exact coefficientLeray_smul_arg k z (c k)

theorem torusSobolevLeray_mem (s : ℕ) (c : TorusSobolev s) :
    Memℓp (sobolevWeightedCoeff s (fourierLerayLinear c.val)) 2 := by
  change Memℓp (sobolevWeightedCoeff s (lerayFourierCoeff c.val)) 2
  apply memℓp_gen' (C := ‖c‖ ^ 2)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    torusSobolev_leray_finite_sum_le s c S

def torusSobolevLerayLinear (s : ℕ) : TorusSobolev s →ₗ[ℂ] TorusSobolev s :=
  torusSobolevLiftLinear s s fourierLerayLinear (torusSobolevLeray_mem s)

@[simp]
theorem torusSobolevLerayLinear_coeff (s : ℕ) (c : TorusSobolev s) :
    (torusSobolevLerayLinear s c).val = lerayFourierCoeff c.val :=
  torusSobolevLiftLinear_coeff s s fourierLerayLinear (torusSobolevLeray_mem s) c

theorem torusSobolevLerayLinear_norm_le (s : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevLerayLinear s c‖ ≤ ‖c‖ := by
  calc
    _ = ‖torusSobolevRepr s (torusSobolevLerayLinear s c)‖ :=
      ((torusSobolevRepr s).norm_map _).symm
    _ ≤ ‖c‖ := by
      apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg c)
      intro S
      simp only [torusSobolevRepr_apply, torusSobolevLerayLinear_coeff]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sobolevWeightedCoeff] using
        torusSobolev_leray_finite_sum_le s c S

theorem torusSobolevLeray_bound (s : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevLerayLinear s c‖ ≤ 1 * ‖c‖ := by
  simpa only [one_mul] using torusSobolevLerayLinear_norm_le s c

def torusSobolevLeray (s : ℕ) : TorusSobolev s →L[ℂ] TorusSobolev s :=
  (torusSobolevLerayLinear s).mkContinuous 1 (torusSobolevLeray_bound s)

@[simp]
theorem torusSobolevLeray_coeff (s : ℕ) (c : TorusSobolev s) :
    (torusSobolevLeray s c).val = lerayFourierCoeff c.val := by
  unfold torusSobolevLeray
  exact (congrArg (fun v : TorusSobolev s => v.val)
    ((torusSobolevLerayLinear s).mkContinuous_apply 1
      (torusSobolevLeray_bound s) c)).trans (torusSobolevLerayLinear_coeff s c)

theorem torusSobolevLeray_norm_le (s : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevLeray s c‖ ≤ ‖c‖ := torusSobolevLerayLinear_norm_le s c

end

end SingularClosure
