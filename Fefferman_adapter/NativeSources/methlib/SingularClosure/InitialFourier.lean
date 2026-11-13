import SingularClosure.FourierIntegral
import SingularClosure.PhysicalProjection

/-!
# Actual Fourier coefficients of admissible initial data

The integrals here are exactly `datumFourierCoeff` from the Galerkin contract.
Integrability follows from continuity on the actual compact Euclidean cube.
Reality is proved by complex conjugation of those integrals. No spectral
reality or integrability premise is introduced in place of the physical datum.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem datumFourierIntegrand_continuous {a : Field}
    (ha : Continuous a) (k : Frequency) (i : Fin 3) :
    Continuous (datumFourierIntegrand a k i) := by
  exact ((fourierCharacter_contDiff k).continuous.star).mul
    (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha))

theorem datumFourierIntegrand_integrableOn {a : Field}
    (ha : Continuous a) (k : Frequency) (i : Fin 3) :
    IntegrableOn (datumFourierIntegrand a k i) unitCube volume :=
  (datumFourierIntegrand_continuous ha k i).continuousOn.integrableOn_compact
    isCompact_unitCube

theorem smoothSigmaZero_fourier_integrable {a : Field}
    (ha : SmoothSigmaZero a) (k : Frequency) (i : Fin 3) :
    IntegrableOn (datumFourierIntegrand a k i) unitCube volume :=
  datumFourierIntegrand_integrableOn ha.smooth.continuous k i

theorem datumFourierIntegrand_neg (a : Field) (k : Frequency) (i : Fin 3)
    (x : Vec) :
    datumFourierIntegrand a (-k) i x = star (datumFourierIntegrand a k i x) := by
  simp [datumFourierIntegrand, fourierCharacter_neg, star_mul, mul_comm]

/-- Fourier reality follows for every real-valued physical field, without a
spectral symmetry assumption. Integrability is independently proved above for
admissible data. -/
theorem datumFourierCoeff_reality (a : Field) :
    SpectralReality (datumFourierCoeff a) := by
  intro k i
  unfold datumFourierCoeff
  simp_rw [datumFourierIntegrand_neg]
  simpa only [Complex.star_def] using
    (integral_conj (f := datumFourierIntegrand a k i)
      (μ := volume.restrict unitCube))

/-- The zeroth Fourier coefficient is the actual spatial mean component. -/
theorem datumFourierCoeff_zero {a : Field}
    (ha : IntegrableOn a unitCube volume) (i : Fin 3) :
    datumFourierCoeff a 0 i = (spatialMean a i : ℂ) := by
  unfold datumFourierCoeff datumFourierIntegrand
  simp only [fourierCharacter, Pi.zero_apply, Int.cast_zero, zero_mul,
    Finset.sum_const_zero, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    star_one, one_mul]
  rw [integral_complex_ofReal]
  congr 1
  exact (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).integral_comp_comm ha

theorem smoothSigmaZero_fourier_meanZero {a : Field}
    (ha : SmoothSigmaZero a) : SpectralMeanZero (datumFourierCoeff a) := by
  intro i
  rw [datumFourierCoeff_zero ha.mean_zero.1, ha.mean_zero.2]
  simp

private theorem integral_unitCube_eq_integral_piCube (f : Vec → ℂ) :
    (∫ x in unitCube, f x) =
      ∫ x in Icc (0 : Fin 3 → ℝ) (fun _ => 1), f (WithLp.toLp 2 x) := by
  have hchange := (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding f unitCube
  have hpre : (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' unitCube =
      Icc (0 : Fin 3 → ℝ) (fun _ => 1) := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
    · intro hx i
      exact ⟨hx.1 i, hx.2 i⟩
  rw [hpre] at hchange
  exact hchange.symm

private theorem insertNth_one_eq_insertNth_zero_add (i : Fin 3) (x : Fin 2 → ℝ) :
    i.insertNth (α := fun _ : Fin 3 => ℝ) 1 x =
      i.insertNth (α := fun _ : Fin 3 => ℝ) 0 x + Pi.single i 1 := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp
  · simp [Fin.succAbove_ne]

/-- The actual divergence integral on a unit product cube vanishes when the
opposite faces of each component agree. This uses Mathlib's divergence theorem. -/
theorem integral_piCube_divergence_eq_zero
    (f : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hp : ∀ i x, f i (x + Pi.single i 1) = f i x) :
    (∫ x in Icc (0 : Fin 3 → ℝ) (fun _ => 1),
      ∑ i : Fin 3, fderiv ℝ (f i) x (Pi.single i 1)) = 0 := by
  have hcont : Continuous (fun x : Fin 3 → ℝ =>
      ∑ i : Fin 3, fderiv ℝ (f i) x (Pi.single i 1)) :=
    continuous_finsetSum _ (fun i _ =>
      ((hf i).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) (fun _ => 1) (by intro i; norm_num)
    f (fun i => fderiv ℝ (f i)) ∅ Set.countable_empty
    (fun i => (hf i).continuous.continuousOn)
    (fun x _ i => ((hf i).differentiable (by simp) x).hasFDerivAt)
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
  calc
    _ = ∑ i : Fin 3,
        ((∫ x in Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1),
          f i (i.insertNth 1 x)) -
         ∫ x in Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1),
          f i (i.insertNth 0 x)) := hdiv
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have he : (fun x : Fin 2 → ℝ => f i (i.insertNth 1 x)) =
          (fun x => f i (i.insertNth 0 x)) := by
        funext x
        rw [insertNth_one_eq_insertNth_zero_add, hp]
      rw [he, sub_self]

/-- Physical Euclidean-coordinate version of periodic integration by parts. -/
theorem integral_unitCube_divergence_eq_zero
    (f : Fin 3 → Vec → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hp : ∀ i x, f i (x + unitVector i) = f i x) :
    (∫ x in unitCube, ∑ i : Fin 3, fderiv ℝ (f i) x (unitVector i)) = 0 := by
  let L : (Fin 3 → ℝ) ≃L[ℝ] Vec :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hL (i : Fin 3) : L (Pi.single i 1) = unitVector i := by
    ext j
    rfl
  have hderiv (i : Fin 3) (x : Fin 3 → ℝ) :
      fderiv ℝ (fun y => f i (L y)) x (Pi.single i 1) =
        fderiv ℝ (f i) (L x) (unitVector i) := by
    have h := ((hf i).differentiable (by simp) (L x)).hasFDerivAt.comp x
      L.hasFDerivAt
    have he := congrArg
      (fun D : (Fin 3 → ℝ) →L[ℝ] ℂ => D (Pi.single i 1)) h.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hL] using he
  rw [integral_unitCube_eq_integral_piCube]
  change (∫ x in Icc (0 : Fin 3 → ℝ) (fun _ => 1),
    ∑ i : Fin 3, fderiv ℝ (f i) (L x) (unitVector i)) = 0
  have h := integral_piCube_divergence_eq_zero (fun i x => f i (L x))
    (fun i => (hf i).comp L.contDiff) (by
      intro i x
      rw [map_add, hL, hp])
  simpa only [hderiv] using h

theorem datumFourierIntegrand_contDiff {a : Field}
    (ha : ContDiff ℝ ∞ a) (k : Frequency) (i : Fin 3) :
    ContDiff ℝ ∞ (datumFourierIntegrand a k i) := by
  have he : datumFourierIntegrand a k i =
      (fun x => fourierCharacter (-k) x * (a x i : ℂ)) := by
    funext x
    simp only [datumFourierIntegrand, fourierCharacter_neg]
  rw [he]
  exact (fourierCharacter_contDiff (-k)).mul
    (Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp ha))

theorem datumFourierIntegrand_periodic {a : Field}
    (ha : SpatialPeriodic a) (k : Frequency) (i : Fin 3) :
    SpatialPeriodic (datumFourierIntegrand a k i) := by
  intro x j
  simp only [datumFourierIntegrand, fourierCharacter_periodic k x j, ha x j]

set_option backward.isDefEq.respectTransparency false in
theorem datumFourierIntegrand_coordinateDerivative {a : Field}
    (ha : Differentiable ℝ a) (k : Frequency) (i : Fin 3) (x : Vec) :
    fderiv ℝ (datumFourierIntegrand a k i) x (unitVector i) =
      star (fourierCharacter k x) * (coordinateDerivative a i x i : ℂ) -
        derivativeSymbol i k * datumFourierIntegrand a k i x := by
  have he : datumFourierIntegrand a k i =
      (fun y => fourierCharacter (-k) y * (a y i : ℂ)) := by
    funext y
    simp only [datumFourierIntegrand, fourierCharacter_neg]
  have ha' := Complex.ofRealCLM.hasFDerivAt.comp x
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x (ha x).hasFDerivAt)
  have hp := (fourierCharacter_hasFDerivAt (-k) x).mul ha'
  have hp' : HasFDerivAt (fun y => fourierCharacter (-k) y * (a y i : ℂ))
      (fourierCharacter (-k) x •
        (Complex.ofRealCLM.comp ((EuclideanSpace.proj i).comp (fderiv ℝ a x))) +
        (a x i : ℂ) • (fourierCharacter (-k) x • fourierPhaseCLM (-k))) x := by
    simpa only [Function.comp_def, Pi.mul_def, Complex.ofRealCLM_apply,
      EuclideanSpace.coe_proj] using hp
  rw [he, hp'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, fourierPhaseCLM_unitVector,
    fourierCharacter_neg]
  unfold derivativeSymbol coordinateDerivative
  simp only [Pi.neg_apply, Int.cast_neg, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_intCast]
  ring

/-- Divergence freedom of the physical smooth periodic datum implies its
Fourier solenoidality. The proof uses actual periodic integration by parts. -/
theorem smoothSigmaZero_fourier_solenoidal {a : Field}
    (ha : SmoothSigmaZero a) : SpectralSolenoidal (datumFourierCoeff a) := by
  intro k
  have hzero := integral_unitCube_divergence_eq_zero
    (fun i => datumFourierIntegrand a k i)
    (fun i => datumFourierIntegrand_contDiff ha.smooth k i)
    (fun i x => datumFourierIntegrand_periodic ha.periodic k i x i)
  have hsum (x : Vec) :
      (∑ i : Fin 3, fderiv ℝ (datumFourierIntegrand a k i) x (unitVector i)) =
        -(∑ i : Fin 3, derivativeSymbol i k * datumFourierIntegrand a k i x) := by
    simp_rw [datumFourierIntegrand_coordinateDerivative
      (ha.smooth.differentiable (by simp))]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum]
    change star (fourierCharacter k x) * (divergence a x : ℂ) - _ = _
    rw [ha.divergence_free x]
    simp
  simp_rw [hsum] at hzero
  rw [integral_neg] at hzero
  have hcoeff : (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff a k i) = 0 := by
    have h := neg_eq_zero.mp hzero
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (smoothSigmaZero_fourier_integrable ha k i).const_mul (derivativeSymbol i k))] at h
    simpa only [integral_const_mul, datumFourierCoeff] using h
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hfactor :
      (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff a k i) =
        C * ∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff a k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast, C]
    ring
  have hC : C ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  rw [hfactor] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left hC

end

end SingularClosure
