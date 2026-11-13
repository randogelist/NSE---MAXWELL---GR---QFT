import QuantumAdapter.Assembly.Fourier
import SingularClosure.PhysicalBilinear

/-! Exact full-mode physical Fourier identities, retaining arbitrary means. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

def fullSynthesis (N : ℕ) (c : FourierCoeff) : Field :=
  fun x => WithLp.toLp 2 (fun i : Fin 3 =>
    (∑ k ∈ fullModes N, fourierCharacter k x * c k i).re)

theorem fullSynthesis_contDiff (N : ℕ) (c : FourierCoeff) :
    ContDiff ℝ ∞ (fullSynthesis N c) := by
  apply (contDiff_piLp 2).2
  intro i
  change ContDiff ℝ ∞ (fun x : Vec =>
    (∑ k ∈ fullModes N, fourierCharacter k x * c k i).re)
  apply Complex.reCLM.contDiff.comp
  apply ContDiff.sum
  intro k hk
  exact (fourierCharacter_contDiff k).mul contDiff_const

@[simp] theorem fullSynthesis_phaseCoeff (N : ℕ) (q : Phase N) :
    fullSynthesis N (phaseCoeff q) = synthesis q := rfl

def complexFullSynthesis (N : ℕ) (c : FourierCoeff) (j : Fin 3) (x : Vec) : ℂ :=
  ∑ k ∈ fullModes N, fourierCharacter k x * c k j


theorem complexFullSynthesis_continuous (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    Continuous (complexFullSynthesis N c j) :=
  continuous_finsetSum _ (fun k _ =>
    (fourierCharacter_contDiff k).continuous.mul continuous_const)


theorem complexFullSynthesis_star (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (j : Fin 3) (x : Vec) :
    star (complexFullSynthesis N c j x) = complexFullSynthesis N c j x := by
  classical
  have hsum : (∑ k ∈ fullModes N, fourierCharacter (-k) x * c (-k) j) =
      ∑ k ∈ fullModes N, fourierCharacter k x * c k j := by
    apply Finset.sum_nbij' (fun k : Frequency => -k) (fun k : Frequency => -k)
      (fun k hk => fullModes_neg_mem hk) (fun k hk => fullModes_neg_mem hk)
    · intro k _
      simp
    · intro k _
      simp
    · intro k _
      rfl
  unfold complexFullSynthesis
  rw [complex_star_finset_sum]
  calc
    _ = ∑ k ∈ fullModes N, fourierCharacter (-k) x * c (-k) j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fourierCharacter_neg, hreal k j]
      simp only [Complex.star_def, map_mul]
    _ = _ := hsum


theorem complexFullSynthesis_eq_ofReal (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (j : Fin 3) (x : Vec) :
    complexFullSynthesis N c j x = (fullSynthesis N c x j : ℂ) := by
  have hi := congrArg Complex.im (complexFullSynthesis_star N c hreal j x)
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith


theorem integral_complexFullSynthesis_inner (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube,
      star (complexFullSynthesis N c j x) * complexFullSynthesis N c j x) =
        ∑ k ∈ fullModes N, (Complex.normSq (c k j) : ℂ) := by
  classical
  unfold complexFullSynthesis
  simp_rw [complex_star_finset_sum]
  rw [integral_unitCube_complex_sum_mul_sum (fullModes N) (fullModes N)
    (fun k x => star (fourierCharacter k x * c k j))
    (fun l x => fourierCharacter l x * c l j)
    (fun k => ((fourierCharacter_contDiff k).continuous.mul continuous_const).star)
    (fun l => (fourierCharacter_contDiff l).continuous.mul continuous_const)]
  simp_rw [integral_complex_character_pair]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · simp only [ite_true, Complex.star_def, Complex.normSq_eq_conj_mul_self]
  · intro l _ hlk
    simp [Ne.symm hlk]
  · intro hnot
    exact (hnot hk).elim


theorem integral_complexFullSynthesis_normSq (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube, Complex.normSq (complexFullSynthesis N c j x)) =
      ∑ k ∈ fullModes N, Complex.normSq (c k j) := by
  have hi : IntegrableOn (fun x : Vec =>
      star (complexFullSynthesis N c j x) * complexFullSynthesis N c j x)
      unitCube volume :=
    ((complexFullSynthesis_continuous N c j).star.mul
      (complexFullSynthesis_continuous N c j)).continuousOn.integrableOn_compact isCompact_unitCube
  calc
    _ = ∫ x in unitCube,
        (star (complexFullSynthesis N c j x) * complexFullSynthesis N c j x).re := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simpa only [Complex.ofReal_re, Complex.star_def] using
        congrArg Complex.re (Complex.normSq_eq_conj_mul_self
          (z := complexFullSynthesis N c j x))
    _ = (∫ x in unitCube,
        star (complexFullSynthesis N c j x) * complexFullSynthesis N c j x).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ := by
      rw [integral_complexFullSynthesis_inner, physical_complex_re_sum]
      simp


theorem FULL_PHYSICAL_COMPONENT_PARSEVAL (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (j : Fin 3) :
    (∫ x in unitCube, (fullSynthesis N c x j) ^ 2) =
      ∑ k ∈ fullModes N, Complex.normSq (c k j) := by
  have heq (x : Vec) : (fullSynthesis N c x j) ^ 2 =
      Complex.normSq (complexFullSynthesis N c j x) := by
    rw [complexFullSynthesis_eq_ofReal N c hreal j x]
    simp [Complex.normSq_apply, pow_two]
  simp_rw [heq]
  exact integral_complexFullSynthesis_normSq N c j


def fullMean (c : FourierCoeff) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => (c 0 i).re)

theorem fullSynthesis_eq_mean_add_source (N : ℕ) (c : FourierCoeff) :
    fullSynthesis N c = fun x => fullMean c + finiteSynthesis N c x := by
  funext x
  ext i
  simp [fullSynthesis, fullMean, fullModes, finiteSynthesis,
    cutoffModes_zero_not_mem, fourierCharacter]

theorem fullSynthesis_eq_finite_of_mean_zero (N : ℕ) (c : FourierCoeff)
    (hc : ∀ i : Fin 3, c 0 i = 0) : fullSynthesis N c = finiteSynthesis N c := by
  rw [fullSynthesis_eq_mean_add_source]
  have hz : fullMean c = 0 := by ext i; simp [fullMean, hc]
  simp [hz]

theorem fullSynthesis_periodic (N : ℕ) (c : FourierCoeff) :
    SpatialPeriodic (fullSynthesis N c) := by
  intro x j
  simp only [fullSynthesis_eq_mean_add_source]
  exact congrArg (fun v : Vec => fullMean c + v) (finiteSynthesis_periodic N c x j)

theorem fullSynthesis_coordinateDerivative (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    coordinateDerivative (fullSynthesis N c) j =
      fullSynthesis N (spectralMultiplier (derivativeSymbol j) c) := by
  rw [fullSynthesis_eq_finite_of_mean_zero N
    (spectralMultiplier (derivativeSymbol j) c)
    (by intro i; simp [spectralMultiplier, derivativeSymbol])]
  rw [← finiteSynthesis_coordinateDerivative]
  funext x
  unfold coordinateDerivative
  have hd := ((finiteSynthesis_contDiff N c).differentiable (by simp) x).hasFDerivAt
  have hs : HasFDerivAt (fun y => fullMean c + finiteSynthesis N c y)
      (fderiv ℝ (finiteSynthesis N c) x) x :=
    (hasFDerivAt_const_add_iff (fullMean c)).mpr hd
  rw [fullSynthesis_eq_mean_add_source, hs.fderiv]

theorem fullSynthesis_add (N : ℕ) (a b : FourierCoeff) :
    fullSynthesis N (a + b) = fullSynthesis N a + fullSynthesis N b := by
  funext x
  ext i
  simp [fullSynthesis, mul_add, Finset.sum_add_distrib]

theorem fullSynthesis_sub (N : ℕ) (a b : FourierCoeff) :
    fullSynthesis N (a - b) = fullSynthesis N a - fullSynthesis N b := by
  funext x
  ext i
  simp [fullSynthesis, mul_sub, Finset.sum_sub_distrib]

theorem synthesis_contDiff (N : ℕ) (q : Phase N) :
    ContDiff ℝ ∞ (synthesis q) := fullSynthesis_contDiff N (phaseCoeff q)

theorem synthesis_periodic (N : ℕ) (q : Phase N) :
    SpatialPeriodic (synthesis q) := fullSynthesis_periodic N (phaseCoeff q)

theorem synthesis_add (N : ℕ) (q r : Phase N) :
    synthesis (q + r) = synthesis q + synthesis r := by
  change fullSynthesis N (phaseCoeff (q + r)) = _
  rw [Assembly.phaseCoeff_add, fullSynthesis_add]
  rfl

theorem synthesis_sub (N : ℕ) (q r : Phase N) :
    synthesis (q - r) = synthesis q - synthesis r := by
  have hc : phaseCoeff (q - r) = phaseCoeff q - phaseCoeff r := by
    funext k i
    by_cases hk : k ∈ fullModes N <;> simp [phaseCoeff, extendCoeff, hk]
  change fullSynthesis N (phaseCoeff (q - r)) = _
  rw [hc, fullSynthesis_sub]
  rfl

theorem integral_synthesis_norm_sq (N : ℕ) (q : Phase N) :
    (∫ x in unitCube, ‖synthesis q x‖ ^ 2) = ‖q‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => (synthesis q x j)^2)
    (μ := volume.restrict unitCube) (fun j _ =>
      (((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
        (synthesis_contDiff N q).continuous).pow 2).continuousOn.integrableOn_compact
          isCompact_unitCube)]
  change (∑ j : Fin 3, ∫ x in unitCube,
    (fullSynthesis N (phaseCoeff q) x j)^2) = _
  simp_rw [FULL_PHYSICAL_COMPONENT_PARSEVAL N (phaseCoeff q) (phaseCoeff_reality q)]
  rw [Finset.sum_comm]
  exact Assembly.energy0_eq_norm_sq N q

theorem integral_complexFullSynthesis_cross (N : ℕ) (a b : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube,
      star (complexFullSynthesis N a j x) * complexFullSynthesis N b j x) =
        ∑ k ∈ fullModes N, star (a k j) * b k j := by
  classical
  unfold complexFullSynthesis
  simp_rw [complex_star_finset_sum]
  rw [integral_unitCube_complex_sum_mul_sum (fullModes N) (fullModes N)
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


theorem FULL_PHYSICAL_COMPONENT_BILINEAR_PARSEVAL (N : ℕ) (a b : FourierCoeff)
    (ha : SpectralReality a) (hb : SpectralReality b) (j : Fin 3) :
    (∫ x in unitCube, fullSynthesis N a x j * fullSynthesis N b x j) =
      ∑ k ∈ fullModes N, (star (a k j) * b k j).re := by
  have hi : IntegrableOn (fun x : Vec =>
      star (complexFullSynthesis N a j x) * complexFullSynthesis N b j x)
      unitCube volume :=
    ((complexFullSynthesis_continuous N a j).star.mul
      (complexFullSynthesis_continuous N b j)).continuousOn.integrableOn_compact isCompact_unitCube
  calc
    _ = ∫ x in unitCube,
        (star (complexFullSynthesis N a j x) * complexFullSynthesis N b j x).re := by
      apply integral_congr_ae
      filter_upwards with x
      rw [complexFullSynthesis_eq_ofReal N a ha, complexFullSynthesis_eq_ofReal N b hb]
      simp
    _ = (∫ x in unitCube,
        star (complexFullSynthesis N a j x) * complexFullSynthesis N b j x).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ := by rw [integral_complexFullSynthesis_cross, physical_complex_re_sum]


theorem FULL_PHYSICAL_BILINEAR_PARSEVAL (N : ℕ) (a b : FourierCoeff)
    (ha : SpectralReality a) (hb : SpectralReality b) :
    (∫ x in unitCube, inner ℝ (fullSynthesis N a x) (fullSynthesis N b x)) =
      ∑ k ∈ fullModes N, ∑ j : Fin 3, (star (a k j) * b k j).re := by
  have hinner (v w : Vec) : inner ℝ v w = ∑ j : Fin 3, v j * w j := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => fullSynthesis N a x j * fullSynthesis N b x j)
    (μ := volume.restrict unitCube) (fun j _ =>
      ((((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
        (fullSynthesis_contDiff N a).continuous).mul
        ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
          (fullSynthesis_contDiff N b).continuous))).continuousOn.integrableOn_compact
          isCompact_unitCube)]
  simp_rw [FULL_PHYSICAL_COMPONENT_BILINEAR_PARSEVAL N a b ha hb]
  exact Finset.sum_comm


theorem integral_complexFullSynthesis_product_coefficient
    (N : ℕ) (a b : FourierCoeff)
    (hb : ∀ k : Frequency, k ∉ fullModes N → ∀ j : Fin 3, b k j = 0)
    (k : Frequency) (i j : Fin 3) :
    (∫ x in unitCube, star (fourierCharacter k x) *
      (complexFullSynthesis N a i x * complexFullSynthesis N b j x)) =
        ∑ p ∈ fullModes N, a p i * b (k - p) j := by
  classical
  have hpoint (x : Vec) : star (fourierCharacter k x) *
      (complexFullSynthesis N a i x * complexFullSynthesis N b j x) =
        (∑ p ∈ fullModes N,
          star (fourierCharacter k x) * (fourierCharacter p x * a p i)) *
        (∑ q ∈ fullModes N, fourierCharacter q x * b q j) := by
    simp only [complexFullSynthesis, ← Finset.mul_sum, mul_assoc]
  simp_rw [hpoint]
  rw [integral_unitCube_complex_sum_mul_sum (fullModes N) (fullModes N)
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
  by_cases hm : k - p ∈ fullModes N
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


theorem datumFourierCoeff_convection_fullSynthesis
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ fullModes N → ∀ j : Fin 3, c k j = 0)
    (hreal : SpectralReality c) :
    datumFourierCoeff (convection (fullSynthesis N c)) = fullTransport N c := by
  funext k i
  have hpoint (x : Vec) : (convection (fullSynthesis N c) x i : ℂ) =
      ∑ j : Fin 3, complexFullSynthesis N c j x *
        complexFullSynthesis N (spectralMultiplier (derivativeSymbol j) c) i x := by
    rw [convection_component_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [fullSynthesis_coordinateDerivative,
      complexFullSynthesis_eq_ofReal N c hreal,
      complexFullSynthesis_eq_ofReal N _ (derivativeMultiplier_reality c hreal j)]
    all_goals rfl
  unfold datumFourierCoeff datumFourierIntegrand
  simp_rw [hpoint, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => star (fourierCharacter k x) *
      (complexFullSynthesis N c j x *
        complexFullSynthesis N (spectralMultiplier (derivativeSymbol j) c) i x))
    (μ := volume.restrict unitCube) (fun j _ =>
      ((fourierCharacter_contDiff k).continuous.star.mul
        ((complexFullSynthesis_continuous N c j).mul
          (complexFullSynthesis_continuous N _ i))).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  have hmul (j : Fin 3) : ∀ k : Frequency, k ∉ fullModes N → ∀ i : Fin 3,
      spectralMultiplier (derivativeSymbol j) c k i = 0 := by
    intro k hk i
    simp [spectralMultiplier, hsupp k hk i]
  have hterm (j : Fin 3) := integral_complexFullSynthesis_product_coefficient N c
    (spectralMultiplier (derivativeSymbol j) c) (hmul j) k j i
  simp_rw [hterm]
  rw [Finset.sum_comm]
  unfold fullTransport
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [spectralMultiplier, derivativeSymbol, Pi.sub_apply]
  ring


theorem integral_fullSynthesis_component_pairing (N : ℕ) (c : FourierCoeff)
    (a : Field) (ha : Continuous a) (i : Fin 3) :
    (∫ x in unitCube, fullSynthesis N c x i * a x i) =
      ∑ k ∈ fullModes N, (star (c k i) * datumFourierCoeff a k i).re := by
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
    (∑ k ∈ fullModes N, fourierCharacter k x * c k i).re * a x i) = _
  simp_rw [physical_complex_re_sum, Finset.sum_mul]
  rw [integral_finsetSum (fullModes N)
    (f := fun k x => (fourierCharacter k x * c k i).re * a x i)
    (μ := volume.restrict unitCube) (fun k _ =>
      ((real_character_continuous k (c k i)).mul hai).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  exact Finset.sum_congr rfl (fun k _ => hmode k)


theorem integral_fullSynthesis_pairing (N : ℕ) (c : FourierCoeff)
    (a : Field) (ha : Continuous a) :
    (∫ x in unitCube, inner ℝ (fullSynthesis N c x) (a x)) =
      ∑ k ∈ fullModes N, ∑ i : Fin 3,
        (star (c k i) * datumFourierCoeff a k i).re := by
  have hinner (v w : Vec) : inner ℝ v w = ∑ i : Fin 3, v i * w i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ
    (f := fun i x => fullSynthesis N c x i * a x i)
    (μ := volume.restrict unitCube) (fun i _ =>
      ((((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
        (fullSynthesis_contDiff N c).continuous).mul
          ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha))).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  simp_rw [integral_fullSynthesis_component_pairing N c a ha]
  exact Finset.sum_comm


end
end QuantumAdapter.Obligations

