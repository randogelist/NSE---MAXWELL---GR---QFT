import SingularClosure.PhysicalParseval
import SingularClosure.GalerkinEnergy

/-! Physical coefficient Parseval for the actual finite Fourier synthesis. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

def complexFiniteSynthesis (N : ℕ) (c : FourierCoeff) (j : Fin 3) (x : Vec) : ℂ :=
  ∑ k ∈ cutoffModes N, fourierCharacter k x * c k j

theorem complexFiniteSynthesis_continuous (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    Continuous (complexFiniteSynthesis N c j) :=
  continuous_finsetSum _ (fun k _ =>
    (fourierCharacter_contDiff k).continuous.mul continuous_const)

theorem complex_star_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    star (∑ i ∈ s, f i) = ∑ i ∈ s, star (f i) :=
  map_sum (starRingEnd ℂ) f s

theorem complexFiniteSynthesis_star (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (j : Fin 3) (x : Vec) :
    star (complexFiniteSynthesis N c j x) = complexFiniteSynthesis N c j x := by
  classical
  have hsum : (∑ k ∈ cutoffModes N, fourierCharacter (-k) x * c (-k) j) =
      ∑ k ∈ cutoffModes N, fourierCharacter k x * c k j := by
    apply Finset.sum_nbij' (fun k : Frequency => -k) (fun k : Frequency => -k)
      (fun k hk => cutoffModes_neg_mem hk) (fun k hk => cutoffModes_neg_mem hk)
    · intro k _
      simp
    · intro k _
      simp
    · intro k _
      rfl
  unfold complexFiniteSynthesis
  rw [complex_star_finset_sum]
  calc
    _ = ∑ k ∈ cutoffModes N, fourierCharacter (-k) x * c (-k) j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fourierCharacter_neg, hreal k j]
      simp only [Complex.star_def, map_mul]
    _ = _ := hsum

theorem complexFiniteSynthesis_eq_ofReal (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (j : Fin 3) (x : Vec) :
    complexFiniteSynthesis N c j x = (finiteSynthesis N c x j : ℂ) := by
  have hi := congrArg Complex.im (complexFiniteSynthesis_star N c hreal j x)
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

theorem integral_unitCube_complex_sum_mul_sum {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (f : ι → Vec → ℂ) (g : κ → Vec → ℂ)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ j, Continuous (g j)) :
    (∫ x in unitCube, (∑ i ∈ s, f i x) * (∑ j ∈ t, g j x)) =
      ∑ i ∈ s, ∑ j ∈ t, ∫ x in unitCube, f i x * g j x := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum s (f := fun i x => ∑ j ∈ t, f i x * g j x)
    (μ := volume.restrict unitCube) (fun i _ =>
    (continuous_finsetSum t (fun j _ => (hf i).mul (hg j))).continuousOn.integrableOn_compact isCompact_unitCube)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum t (f := fun j x => f i x * g j x)
    (μ := volume.restrict unitCube) (fun j _ =>
    ((hf i).mul (hg j)).continuousOn.integrableOn_compact isCompact_unitCube)

theorem integral_complex_character_pair (k l : Frequency) (z w : ℂ) :
    (∫ x in unitCube,
      star (fourierCharacter k x * z) * (fourierCharacter l x * w)) =
        if k = l then star z * w else 0 := by
  classical
  calc
    _ = ∫ x in unitCube, (star z * w) *
        (star (fourierCharacter k x) * fourierCharacter l x) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [Complex.star_def, map_mul]
      ring
    _ = (star z * w) * (if k = l then 1 else 0) := by
      rw [integral_const_mul, INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY]
    _ = _ := by split_ifs <;> simp

theorem integral_complexFiniteSynthesis_inner (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube,
      star (complexFiniteSynthesis N c j x) * complexFiniteSynthesis N c j x) =
        ∑ k ∈ cutoffModes N, (Complex.normSq (c k j) : ℂ) := by
  classical
  unfold complexFiniteSynthesis
  simp_rw [complex_star_finset_sum]
  rw [integral_unitCube_complex_sum_mul_sum (cutoffModes N) (cutoffModes N)
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

theorem integral_complexFiniteSynthesis_normSq (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube, Complex.normSq (complexFiniteSynthesis N c j x)) =
      ∑ k ∈ cutoffModes N, Complex.normSq (c k j) := by
  have hi : IntegrableOn (fun x : Vec =>
      star (complexFiniteSynthesis N c j x) * complexFiniteSynthesis N c j x)
      unitCube volume :=
    ((complexFiniteSynthesis_continuous N c j).star.mul
      (complexFiniteSynthesis_continuous N c j)).continuousOn.integrableOn_compact isCompact_unitCube
  calc
    _ = ∫ x in unitCube,
        (star (complexFiniteSynthesis N c j x) * complexFiniteSynthesis N c j x).re := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simpa only [Complex.ofReal_re, Complex.star_def] using
        congrArg Complex.re (Complex.normSq_eq_conj_mul_self
          (z := complexFiniteSynthesis N c j x))
    _ = (∫ x in unitCube,
        star (complexFiniteSynthesis N c j x) * complexFiniteSynthesis N c j x).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ := by
      rw [integral_complexFiniteSynthesis_inner, physical_complex_re_sum]
      simp

theorem FINITE_PHYSICAL_COMPONENT_PARSEVAL (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (j : Fin 3) :
    (∫ x in unitCube, (finiteSynthesis N c x j) ^ 2) =
      ∑ k ∈ cutoffModes N, Complex.normSq (c k j) := by
  have heq (x : Vec) : (finiteSynthesis N c x j) ^ 2 =
      Complex.normSq (complexFiniteSynthesis N c j x) := by
    rw [complexFiniteSynthesis_eq_ofReal N c hreal j x]
    simp [Complex.normSq_apply, pow_two]
  simp_rw [heq]
  exact integral_complexFiniteSynthesis_normSq N c j

/-- Physical squared L2 norm, computed directly from the three real components. -/
def physicalEnergy (v : Field) : ℝ :=
  ∫ x in unitCube, ∑ j : Fin 3, (v x j) ^ 2

theorem physicalEnergy_eq_integral_norm_sq (v : Field) :
    physicalEnergy v = ∫ x in unitCube, ‖v x‖ ^ 2 := by
  simp only [physicalEnergy, EuclideanSpace.real_norm_sq_eq]

theorem gradientSquareDensity_eq_sum_norm_sq (v : Field) (x : Vec) :
    gradientSquareDensity v x =
      ∑ i : Fin 3, ‖coordinateDerivative v i x‖ ^ 2 := by
  simp only [gradientSquareDensity, EuclideanSpace.real_norm_sq_eq]

theorem FINITE_PHYSICAL_ENERGY_PARSEVAL (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    physicalEnergy (finiteSynthesis N c) = coefficientEnergy N c := by
  unfold physicalEnergy
  rw [integral_finsetSum Finset.univ
    (f := fun j x => (finiteSynthesis N c x j) ^ 2)
    (μ := volume.restrict unitCube) (fun j _ =>
    (((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
      (finiteSynthesis_contDiff N c).continuous).pow 2).continuousOn.integrableOn_compact isCompact_unitCube)]
  simp_rw [FINITE_PHYSICAL_COMPONENT_PARSEVAL N c hreal]
  exact Finset.sum_comm

theorem derivativeSymbol_reality (i : Fin 3) (k : Frequency) :
    derivativeSymbol i (-k) = star (derivativeSymbol i k) := by
  simp [derivativeSymbol, Complex.star_def]

theorem derivativeMultiplier_reality (c : FourierCoeff) (hreal : SpectralReality c)
    (i : Fin 3) : SpectralReality (spectralMultiplier (derivativeSymbol i) c) := by
  intro k j
  simp only [spectralMultiplier, derivativeSymbol_reality, hreal k j,
    Complex.star_def, map_mul]

theorem normSq_derivativeMultiplier (c : FourierCoeff) (i j : Fin 3) (k : Frequency) :
    Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j) =
      (2 * Real.pi * (k i : ℝ)) ^ 2 * Complex.normSq (c k j) := by
  rw [spectralMultiplier, Complex.normSq_mul]
  congr 1
  simp [derivativeSymbol, Complex.normSq_apply, pow_two]

theorem FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    (∫ x in unitCube, gradientSquareDensity (finiteSynthesis N c) x) =
      coefficientDissipation N c := by
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in unitCube, (coordinateDerivative (finiteSynthesis N c) i x j) ^ 2 :=
      integral_gradientSquareDensity (finiteSynthesis_contDiff N c)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k ∈ cutoffModes N,
        Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteSynthesis_coordinateDerivative]
      exact FINITE_PHYSICAL_COMPONENT_PARSEVAL N _ (derivativeMultiplier_reality c hreal i) j
    _ = ∑ k ∈ cutoffModes N, ∑ j : Fin 3, ∑ i : Fin 3,
        Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j) := by
      calc
        _ = ∑ i : Fin 3, ∑ k ∈ cutoffModes N, ∑ j : Fin 3,
            Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = ∑ k ∈ cutoffModes N, ∑ i : Fin 3, ∑ j : Fin 3,
            Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k _
          exact Finset.sum_comm
    _ = coefficientDissipation N c := by
      unfold coefficientDissipation
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [normSq_derivativeMultiplier]
      unfold galerkinFreqSq
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem FINITE_PHYSICAL_ENSTROPHY_PARSEVAL (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    physicalEnstrophy (finiteSynthesis N c) = ENNReal.ofReal (coefficientDissipation N c) := by
  rw [physicalEnstrophy_eq_ofReal_integral (finiteSynthesis_contDiff N c),
    FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal]

end

end SingularClosure
