import SingularClosure.SobolevL2Realization
import SingularClosure.PhysicalProjection

/-!
# Absolutely convergent fixed-frequency transport on H0

The untruncated tensor convolution is absolutely summable by the actual l2
Cauchy--Schwarz inequality. Its divergence-form coefficient is a continuous
bilinear functional on H0 x H0. Under the concrete finite support and
solenoidal conditions it agrees with the actual Galerkin transport formula.
Identification with physical distributional products remains a separate edge.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ENNReal lp

namespace SingularClosure

noncomputable section

def frequencyReflection (k : Frequency) : Frequency ≃ Frequency where
  toFun p := k - p
  invFun p := k - p
  left_inv p := by
    funext j
    change k j - (k j - p j) = p j
    omega
  right_inv p := by
    funext j
    change k j - (k j - p j) = p j
    omega

def reflectedFourierSequence (k : Frequency) (a : FourierSequenceL2) : FourierSequenceL2 :=
  ⟨fun p => a (k - p), by
    apply memℓp_gen
    have h := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [Function.comp_def] using!
      (h.comp_injective (i := fun p : Frequency => k - p)
        (frequencyReflection k).injective)⟩

@[simp]
theorem reflectedFourierSequence_apply (k p : Frequency) (a : FourierSequenceL2) :
    reflectedFourierSequence k a p = a (k - p) := rfl

theorem reflectedFourierSequence_norm (k : Frequency) (a : FourierSequenceL2) :
    ‖reflectedFourierSequence k a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hleft := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (reflectedFourierSequence k a)
  have hright := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) a
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, reflectedFourierSequence_apply]
    at hleft hright
  rw [hleft, hright]
  exact (frequencyReflection k).tsum_eq (fun p => ‖a p‖ ^ 2)

theorem fourierVectorComponent_norm_le (c : FourierVectorSequence) (i : Fin 3) :
    ‖fourierVectorComponent c i‖ ≤ ‖c‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ ≤ ∑ j : Fin 3, ‖fourierVectorComponent c j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ = _ := fourierVectorComponent_sum_norm_sq c

def sobolevComponentSequence (c : TorusSobolev 0) (i : Fin 3) : FourierSequenceL2 :=
  fourierVectorComponent (torusSobolevRepr 0 c) i

@[simp]
theorem sobolevComponentSequence_apply (c : TorusSobolev 0) (i : Fin 3)
    (k : Frequency) : sobolevComponentSequence c i k = c.val k i := by
  simp [sobolevComponentSequence, fourierVectorComponent_apply, torusSobolevRepr_apply]

theorem sobolevComponentSequence_norm_le (c : TorusSobolev 0) (i : Fin 3) :
    ‖sobolevComponentSequence c i‖ ≤ ‖c‖ := by
  exact (fourierVectorComponent_norm_le (torusSobolevRepr 0 c) i).trans_eq
    ((torusSobolevRepr 0).norm_map c)

/-- The actual, untruncated fixed-frequency tensor convolution. -/
def fourierTensorCoefficient (k : Frequency) (j i : Fin 3)
    (c d : TorusSobolev 0) : ℂ :=
  ∑' p : Frequency, c.val p j * d.val (k - p) i

theorem fourierTensorCoefficient_summable_norm (k : Frequency) (j i : Fin 3)
    (c d : TorusSobolev 0) :
    Summable (fun p : Frequency => ‖c.val p j * d.val (k - p) i‖) := by
  have h := lp.summable_mul
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal from by
      rw [Real.holderConjugate_iff]; norm_num)
    (sobolevComponentSequence c j)
    (reflectedFourierSequence k (sobolevComponentSequence d i))
  simpa only [norm_mul, reflectedFourierSequence_apply, sobolevComponentSequence_apply] using h

theorem fourierTensorCoefficient_summable (k : Frequency) (j i : Fin 3)
    (c d : TorusSobolev 0) :
    Summable (fun p : Frequency => c.val p j * d.val (k - p) i) :=
  (fourierTensorCoefficient_summable_norm k j i c d).of_norm

theorem fourierTensorCoefficient_norm_le (k : Frequency) (j i : Fin 3)
    (c d : TorusSobolev 0) : ‖fourierTensorCoefficient k j i c d‖ ≤ ‖c‖ * ‖d‖ := by
  have hh := lp.tsum_mul_le_mul_norm'
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal from by
      rw [Real.holderConjugate_iff]; norm_num)
    (sobolevComponentSequence c j)
    (reflectedFourierSequence k (sobolevComponentSequence d i))
  simp only [reflectedFourierSequence_apply, sobolevComponentSequence_apply,
    reflectedFourierSequence_norm] at hh
  calc
    _ ≤ ∑' p : Frequency, ‖c.val p j * d.val (k - p) i‖ :=
      norm_tsum_le_tsum_norm (fourierTensorCoefficient_summable_norm k j i c d)
    _ = ∑' p : Frequency, ‖c.val p j‖ * ‖d.val (k - p) i‖ :=
      tsum_congr (fun p => norm_mul _ _)
    _ ≤ ‖sobolevComponentSequence c j‖ * ‖sobolevComponentSequence d i‖ := hh
    _ ≤ ‖c‖ * ‖d‖ := mul_le_mul (sobolevComponentSequence_norm_le c j)
      (sobolevComponentSequence_norm_le d i) (norm_nonneg _) (norm_nonneg _)

theorem fourierTensorCoefficient_add_left (k : Frequency) (j i : Fin 3)
    (c e d : TorusSobolev 0) :
    fourierTensorCoefficient k j i (c + e) d =
      fourierTensorCoefficient k j i c d + fourierTensorCoefficient k j i e d := by
  change (∑' p : Frequency, (c.val p j + e.val p j) * d.val (k - p) i) = _
  simp_rw [add_mul]
  exact (fourierTensorCoefficient_summable k j i c d).tsum_add
    (fourierTensorCoefficient_summable k j i e d)

theorem fourierTensorCoefficient_add_right (k : Frequency) (j i : Fin 3)
    (c d e : TorusSobolev 0) :
    fourierTensorCoefficient k j i c (d + e) =
      fourierTensorCoefficient k j i c d + fourierTensorCoefficient k j i c e := by
  change (∑' p : Frequency, c.val p j * (d.val (k - p) i + e.val (k - p) i)) = _
  simp_rw [mul_add]
  exact (fourierTensorCoefficient_summable k j i c d).tsum_add
    (fourierTensorCoefficient_summable k j i c e)

theorem fourierTensorCoefficient_smul_left (k : Frequency) (j i : Fin 3)
    (z : ℂ) (c d : TorusSobolev 0) :
    fourierTensorCoefficient k j i (z • c) d = z * fourierTensorCoefficient k j i c d := by
  change (∑' p : Frequency, (z * c.val p j) * d.val (k - p) i) = _
  simp only [mul_assoc]
  exact (fourierTensorCoefficient_summable k j i c d).tsum_mul_left z

theorem fourierTensorCoefficient_smul_right (k : Frequency) (j i : Fin 3)
    (z : ℂ) (c d : TorusSobolev 0) :
    fourierTensorCoefficient k j i c (z • d) = z * fourierTensorCoefficient k j i c d := by
  change (∑' p : Frequency, c.val p j * (z * d.val (k - p) i)) = _
  calc
    _ = ∑' p : Frequency, z * (c.val p j * d.val (k - p) i) := by
      apply tsum_congr
      intro p
      ring
    _ = _ := (fourierTensorCoefficient_summable k j i c d).tsum_mul_left z

def fourierTensorLinear (k : Frequency) (j i : Fin 3) :
    TorusSobolev 0 →ₗ[ℂ] TorusSobolev 0 →ₗ[ℂ] ℂ where
  toFun c :=
    { toFun := fourierTensorCoefficient k j i c
      map_add' := fun d e => fourierTensorCoefficient_add_right k j i c d e
      map_smul' := fun z d => fourierTensorCoefficient_smul_right k j i z c d }
  map_add' c e := by
    ext d
    exact fourierTensorCoefficient_add_left k j i c e d
  map_smul' z c := by
    ext d
    exact fourierTensorCoefficient_smul_left k j i z c d

/-- A genuine bounded complex-bilinear fixed-frequency tensor coefficient. -/
def fourierTensorBilinear (k : Frequency) (j i : Fin 3) :
    TorusSobolev 0 →L[ℂ] TorusSobolev 0 →L[ℂ] ℂ :=
  (fourierTensorLinear k j i).mkContinuous₂ 1
    (fun c d => by
      change ‖fourierTensorCoefficient k j i c d‖ ≤ 1 * ‖c‖ * ‖d‖
      simpa only [one_mul] using fourierTensorCoefficient_norm_le k j i c d)

@[simp]
theorem fourierTensorBilinear_apply (k : Frequency) (j i : Fin 3)
    (c d : TorusSobolev 0) :
    fourierTensorBilinear k j i c d = fourierTensorCoefficient k j i c d := rfl

/-- Divergence-form transport; the derivative acts on the fixed output frequency. -/
def divergenceTransportCoefficient (k : Frequency) (i : Fin 3) :
    TorusSobolev 0 →L[ℂ] TorusSobolev 0 →L[ℂ] ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k • fourierTensorBilinear k j i

theorem divergenceTransportCoefficient_apply (k : Frequency) (i : Fin 3)
    (c d : TorusSobolev 0) :
    divergenceTransportCoefficient k i c d =
      ∑ j : Fin 3, derivativeSymbol j k *
        (∑' p : Frequency, c.val p j * d.val (k - p) i) := by
  simp [divergenceTransportCoefficient, fourierTensorCoefficient]

theorem divergenceTransportCoefficient_continuous (k : Frequency) (i : Fin 3) :
    Continuous (fun q : TorusSobolev 0 × TorusSobolev 0 =>
      divergenceTransportCoefficient k i q.1 q.2) :=
  ((divergenceTransportCoefficient k i).continuous.comp continuous_fst).clm_apply continuous_snd

theorem fourierTensorCoefficient_eq_sum (N : ℕ) (k : Frequency) (j i : Fin 3)
    (c d : TorusSobolev 0)
    (hsupp : ∀ p : Frequency, p ∉ cutoffModes N → ∀ l : Fin 3, c.val p l = 0) :
    fourierTensorCoefficient k j i c d =
      ∑ p ∈ cutoffModes N, c.val p j * d.val (k - p) i := by
  classical
  unfold fourierTensorCoefficient
  apply tsum_eq_sum
  intro p hp
  rw [hsupp p hp j, zero_mul]

theorem derivativeSymbol_sub (j : Fin 3) (k p : Frequency) :
    derivativeSymbol j (k - p) = derivativeSymbol j k - derivativeSymbol j p := by
  simp only [derivativeSymbol, Pi.sub_apply]
  push_cast
  ring

theorem solenoidal_derivativeSymbol_sum (c : FourierCoeff)
    (hc : SpectralSolenoidal c) (p : Frequency) :
    (∑ j : Fin 3, derivativeSymbol j p * c p j) = 0 := by
  calc
    _ = (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        (∑ j : Fin 3, (p j : ℂ) * c p j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring
    _ = 0 := by rw [hc p, mul_zero]

/-- Exact agreement with the actual finite Galerkin transport under its genuine constraints. -/
theorem coefficientTransport_eq_divergenceTransport (N : ℕ) (c : TorusSobolev 0)
    (hsupp : ∀ p : Frequency, p ∉ cutoffModes N → ∀ i : Fin 3, c.val p i = 0)
    (hsol : SpectralSolenoidal c.val) (k : Frequency) (i : Fin 3) :
    coefficientTransport N c.val k i = divergenceTransportCoefficient k i c c := by
  classical
  have hterm (p : Frequency) :
      (∑ j : Fin 3, c.val p j * derivativeSymbol j (k - p)) =
        ∑ j : Fin 3, derivativeSymbol j k * c.val p j := by
    simp_rw [derivativeSymbol_sub]
    calc
      _ = (∑ j : Fin 3, derivativeSymbol j k * c.val p j) -
          (∑ j : Fin 3, derivativeSymbol j p * c.val p j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [solenoidal_derivativeSymbol_sum c.val hsol p, sub_zero]
  rw [divergenceTransportCoefficient_apply]
  change (∑ p ∈ cutoffModes N,
    (∑ j : Fin 3, c.val p j * derivativeSymbol j (k - p)) * c.val (k - p) i) = _
  simp_rw [hterm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = derivativeSymbol j k *
        (∑ p ∈ cutoffModes N, c.val p j * c.val (k - p) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := congrArg (fun z : ℂ => derivativeSymbol j k * z)
      (fourierTensorCoefficient_eq_sum N k j i c c hsupp).symm

end

end SingularClosure
