import SingularClosure.FiniteHessian
import SingularClosure.EnstrophyInequality

/-! Physical Fourier pairings and the actual Galerkin transport convolution. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem integral_complexFiniteSynthesis_cross (N : ℕ) (a b : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube,
      star (complexFiniteSynthesis N a j x) * complexFiniteSynthesis N b j x) =
        ∑ k ∈ cutoffModes N, star (a k j) * b k j := by
  classical
  unfold complexFiniteSynthesis
  simp_rw [complex_star_finset_sum]
  rw [integral_unitCube_complex_sum_mul_sum (cutoffModes N) (cutoffModes N)
    (fun k x => star (fourierCharacter k x * a k j))
    (fun l x => fourierCharacter l x * b l j)
    (fun k => ((fourierCharacter_contDiff k).continuous.mul continuous_const).star)
    (fun l => (fourierCharacter_contDiff l).continuous.mul continuous_const)]
  simp_rw [integral_complex_character_pair]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hlk
    simp [Ne.symm hlk]
  · intro hnot
    exact (hnot hk).elim

theorem FINITE_PHYSICAL_COMPONENT_BILINEAR_PARSEVAL (N : ℕ) (a b : FourierCoeff)
    (ha : SpectralReality a) (hb : SpectralReality b) (j : Fin 3) :
    (∫ x in unitCube, finiteSynthesis N a x j * finiteSynthesis N b x j) =
      ∑ k ∈ cutoffModes N, (star (a k j) * b k j).re := by
  have hi : IntegrableOn (fun x : Vec =>
      star (complexFiniteSynthesis N a j x) * complexFiniteSynthesis N b j x)
      unitCube volume :=
    ((complexFiniteSynthesis_continuous N a j).star.mul
      (complexFiniteSynthesis_continuous N b j)).continuousOn.integrableOn_compact isCompact_unitCube
  calc
    _ = ∫ x in unitCube,
        (star (complexFiniteSynthesis N a j x) * complexFiniteSynthesis N b j x).re := by
      apply integral_congr_ae
      filter_upwards with x
      rw [complexFiniteSynthesis_eq_ofReal N a ha, complexFiniteSynthesis_eq_ofReal N b hb]
      simp
    _ = (∫ x in unitCube,
        star (complexFiniteSynthesis N a j x) * complexFiniteSynthesis N b j x).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ := by rw [integral_complexFiniteSynthesis_cross, physical_complex_re_sum]

theorem FINITE_PHYSICAL_BILINEAR_PARSEVAL (N : ℕ) (a b : FourierCoeff)
    (ha : SpectralReality a) (hb : SpectralReality b) :
    (∫ x in unitCube, inner ℝ (finiteSynthesis N a x) (finiteSynthesis N b x)) =
      ∑ k ∈ cutoffModes N, ∑ j : Fin 3, (star (a k j) * b k j).re := by
  have hinner (v w : Vec) : inner ℝ v w = ∑ j : Fin 3, v j * w j := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => finiteSynthesis N a x j * finiteSynthesis N b x j)
    (μ := volume.restrict unitCube) (fun j _ =>
      ((((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
        (finiteSynthesis_contDiff N a).continuous).mul
        ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
          (finiteSynthesis_contDiff N b).continuous))).continuousOn.integrableOn_compact
          isCompact_unitCube)]
  simp_rw [FINITE_PHYSICAL_COMPONENT_BILINEAR_PARSEVAL N a b ha hb]
  exact Finset.sum_comm

theorem convection_eq_sum_coordinateDerivative (v : Field) (x : Vec) :
    convection v x = ∑ j : Fin 3, v x j • coordinateDerivative v j x := by
  have hx : (∑ j : Fin 3, v x j • unitVector j) = v x := by
    ext i
    fin_cases i <;> simp [unitVector, Fin.sum_univ_succ, Pi.single_apply]
  have h := congrArg (fderiv ℝ v x) hx
  simpa only [map_sum, map_smul, convection, coordinateDerivative] using h.symm

theorem convection_component_eq_sum (v : Field) (x : Vec) (i : Fin 3) :
    convection v x i = ∑ j : Fin 3, v x j * coordinateDerivative v j x i := by
  have h := congrArg (EuclideanSpace.proj i : Vec →L[ℝ] ℝ)
    (convection_eq_sum_coordinateDerivative v x)
  simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.coe_proj] using h

theorem integral_character_triple (k p q : Frequency) (z w : ℂ) :
    (∫ x in unitCube, (star (fourierCharacter k x) *
      (fourierCharacter p x * z)) * (fourierCharacter q x * w)) =
        if k = p + q then z * w else 0 := by
  classical
  calc
    _ = ∫ x in unitCube, (z * w) *
        (star (fourierCharacter k x) * fourierCharacter (p + q) x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← fourierCharacter_mul]
      ring
    _ = (z * w) * (if k = p + q then 1 else 0) := by
      rw [integral_const_mul, INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY]
    _ = _ := by split_ifs <;> simp

theorem integral_complexFiniteSynthesis_product_coefficient
    (N : ℕ) (a b : FourierCoeff)
    (hb : ∀ k : Frequency, k ∉ cutoffModes N → ∀ j : Fin 3, b k j = 0)
    (k : Frequency) (i j : Fin 3) :
    (∫ x in unitCube, star (fourierCharacter k x) *
      (complexFiniteSynthesis N a i x * complexFiniteSynthesis N b j x)) =
        ∑ p ∈ cutoffModes N, a p i * b (k - p) j := by
  classical
  have hpoint (x : Vec) : star (fourierCharacter k x) *
      (complexFiniteSynthesis N a i x * complexFiniteSynthesis N b j x) =
        (∑ p ∈ cutoffModes N,
          star (fourierCharacter k x) * (fourierCharacter p x * a p i)) *
        (∑ q ∈ cutoffModes N, fourierCharacter q x * b q j) := by
    simp only [complexFiniteSynthesis, ← Finset.mul_sum, mul_assoc]
  simp_rw [hpoint]
  rw [integral_unitCube_complex_sum_mul_sum (cutoffModes N) (cutoffModes N)
    (fun p x => star (fourierCharacter k x) * (fourierCharacter p x * a p i))
    (fun q x => fourierCharacter q x * b q j)
    (fun p => (fourierCharacter_contDiff k).continuous.star.mul
      ((fourierCharacter_contDiff p).continuous.mul continuous_const))
    (fun q => (fourierCharacter_contDiff q).continuous.mul continuous_const)]
  simp_rw [integral_character_triple]
  apply Finset.sum_congr rfl
  intro p _
  have heq (q : Frequency) : k = p + q ↔ q = k - p := by
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      rw [h]
      abel
  simp_rw [heq]
  by_cases hm : k - p ∈ cutoffModes N
  · rw [Finset.sum_eq_single (k - p)]
    · simp
    · intro q _ hq
      simp [hq]
    · intro hnot
      exact (hnot hm).elim
  · rw [hb (k - p) hm j, mul_zero]
    apply Finset.sum_eq_zero
    intro q hq
    have hne : q ≠ k - p := by intro he; exact hm (he ▸ hq)
    simp [hne]

theorem datumFourierCoeff_convection_finiteSynthesis
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ j : Fin 3, c k j = 0)
    (hreal : SpectralReality c) :
    datumFourierCoeff (convection (finiteSynthesis N c)) = coefficientTransport N c := by
  funext k i
  have hpoint (x : Vec) : (convection (finiteSynthesis N c) x i : ℂ) =
      ∑ j : Fin 3, complexFiniteSynthesis N c j x *
        complexFiniteSynthesis N (spectralMultiplier (derivativeSymbol j) c) i x := by
    rw [convection_component_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [finiteSynthesis_coordinateDerivative,
      complexFiniteSynthesis_eq_ofReal N c hreal,
      complexFiniteSynthesis_eq_ofReal N _ (derivativeMultiplier_reality c hreal j)]
    all_goals rfl
  unfold datumFourierCoeff datumFourierIntegrand
  simp_rw [hpoint, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => star (fourierCharacter k x) *
      (complexFiniteSynthesis N c j x *
        complexFiniteSynthesis N (spectralMultiplier (derivativeSymbol j) c) i x))
    (μ := volume.restrict unitCube) (fun j _ =>
      ((fourierCharacter_contDiff k).continuous.star.mul
        ((complexFiniteSynthesis_continuous N c j).mul
          (complexFiniteSynthesis_continuous N _ i))).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  have hmul (j : Fin 3) : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3,
      spectralMultiplier (derivativeSymbol j) c k i = 0 := by
    intro k hk i
    simp [spectralMultiplier, hsupp k hk i]
  have hterm (j : Fin 3) := integral_complexFiniteSynthesis_product_coefficient N c
    (spectralMultiplier (derivativeSymbol j) c) (hmul j) k j i
  simp_rw [hterm]
  rw [Finset.sum_comm]
  unfold coefficientTransport
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [spectralMultiplier, derivativeSymbol, Pi.sub_apply]
  ring

theorem integral_finiteSynthesis_component_pairing (N : ℕ) (c : FourierCoeff)
    (a : Field) (ha : Continuous a) (i : Fin 3) :
    (∫ x in unitCube, finiteSynthesis N c x i * a x i) =
      ∑ k ∈ cutoffModes N, (star (c k i) * datumFourierCoeff a k i).re := by
  have hai : Continuous (fun x : Vec => a x i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha
  have hmode (k : Frequency) :
      (∫ x in unitCube, (fourierCharacter k x * c k i).re * a x i) =
        (star (c k i) * datumFourierCoeff a k i).re := by
    have hi : IntegrableOn (fun x : Vec => star (c k i) * datumFourierIntegrand a k i x)
        unitCube volume :=
      (continuous_const.mul ((fourierCharacter_contDiff k).continuous.star.mul
        (Complex.continuous_ofReal.comp hai))).continuousOn.integrableOn_compact isCompact_unitCube
    calc
      _ = ∫ x in unitCube, (star (c k i) * datumFourierIntegrand a k i x).re := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [datumFourierIntegrand, Complex.mul_re, Complex.mul_im, Complex.star_def,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      _ = (∫ x in unitCube, star (c k i) * datumFourierIntegrand a k i x).re :=
        Complex.reCLM.integral_comp_comm hi
      _ = _ := by
        rw [integral_const_mul]
        all_goals rfl
  change (∫ x in unitCube,
    (∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re * a x i) = _
  simp_rw [physical_complex_re_sum, Finset.sum_mul]
  rw [integral_finsetSum (cutoffModes N)
    (f := fun k x => (fourierCharacter k x * c k i).re * a x i)
    (μ := volume.restrict unitCube) (fun k _ =>
      ((real_character_continuous k (c k i)).mul hai).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  exact Finset.sum_congr rfl (fun k _ => hmode k)

theorem integral_finiteSynthesis_pairing (N : ℕ) (c : FourierCoeff)
    (a : Field) (ha : Continuous a) :
    (∫ x in unitCube, inner ℝ (finiteSynthesis N c x) (a x)) =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (star (c k i) * datumFourierCoeff a k i).re := by
  have hinner (v w : Vec) : inner ℝ v w = ∑ i : Fin 3, v i * w i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ
    (f := fun i x => finiteSynthesis N c x i * a x i)
    (μ := volume.restrict unitCube) (fun i _ =>
      ((((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
        (finiteSynthesis_contDiff N c).continuous).mul
          ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha))).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  simp_rw [integral_finiteSynthesis_component_pairing N c a ha]
  exact Finset.sum_comm

theorem convection_continuous {a : Field} (ha : ContDiff ℝ ∞ a) :
    Continuous (convection a) :=
  (ha.continuous_fderiv (by simp)).clm_apply ha.continuous

/-- The nonlinear Fourier enstrophy power is the literal physical trilinear pairing. -/
theorem coefficientEnstrophyNonlinearPower_eq_physical
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    coefficientEnstrophyNonlinearPower N c =
      -(∫ x in unitCube, inner ℝ (convection (finiteSynthesis N c) x)
        (laplacian (finiteSynthesis N c) x)) := by
  rw [finiteSynthesis_laplacian]
  have hswap :
      (∫ x in unitCube, inner ℝ (convection (finiteSynthesis N c) x)
        (finiteSynthesis N (laplacianCoefficient c) x)) =
      ∫ x in unitCube, inner ℝ (finiteSynthesis N (laplacianCoefficient c) x)
        (convection (finiteSynthesis N c) x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact real_inner_comm _ _
  rw [hswap]
  rw [integral_finiteSynthesis_pairing N (laplacianCoefficient c) _
    (convection_continuous (finiteSynthesis_contDiff N c)),
    datumFourierCoeff_convection_finiteSynthesis N c hsupp hreal,
    coefficientEnstrophyNonlinearPower_eq_transport N c hsol]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [physical_complex_re_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hscalar (r : ℝ) (z w : ℂ) :
      r * (star z * w).re = -(star (-(r : ℂ) * z) * w).re := by
    simp [Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  exact hscalar (laplacianFrequency k) (c k i) (coefficientTransport N c k i)

end

end SingularClosure
