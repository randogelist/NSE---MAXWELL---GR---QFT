import SingularClosure.FourierIntegral
import SingularClosure.PhysicalProjection

/-! Actual finite physical orthogonality and gradient Pythagoras. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem real_character_continuous (k : Frequency) (z : ℂ) :
    Continuous (fun x : Vec => (fourierCharacter k x * z).re) :=
  Complex.reCLM.continuous.comp
    ((fourierCharacter_contDiff k).continuous.mul continuous_const)

theorem real_character_product_continuous (k l : Frequency) (z w : ℂ) :
    Continuous (fun x : Vec =>
      (fourierCharacter k x * z).re * (fourierCharacter l x * w).re) :=
  (real_character_continuous k z).mul (real_character_continuous l w)

theorem integral_real_character_product_zero (k l : Frequency)
    (hplus : k + l ≠ 0) (hminus : -k + l ≠ 0) (z w : ℂ) :
    (∫ x in unitCube,
      (fourierCharacter k x * z).re * (fourierCharacter l x * w).re) = 0 := by
  have hfirst : IntegrableOn
      (fun x : Vec => fourierCharacter (k + l) x * (z * w)) unitCube volume :=
    ((fourierCharacter_contDiff (k + l)).continuous.mul continuous_const).continuousOn.integrableOn_compact isCompact_unitCube
  have hsecond : IntegrableOn
      (fun x : Vec => fourierCharacter (-k + l) x * (star z * w)) unitCube volume :=
    ((fourierCharacter_contDiff (-k + l)).continuous.mul continuous_const).continuousOn.integrableOn_compact isCompact_unitCube
  have hid (x : Vec) :
      (2 : ℝ) * ((fourierCharacter k x * z).re * (fourierCharacter l x * w).re) =
        (fourierCharacter (k + l) x * (z * w)).re +
        (fourierCharacter (-k + l) x * (star z * w)).re := by
    rw [← fourierCharacter_mul k l, ← fourierCharacter_mul (-k) l,
      fourierCharacter_neg]
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  have htwo : (2 : ℝ) * (∫ x in unitCube,
      (fourierCharacter k x * z).re * (fourierCharacter l x * w).re) = 0 := by
    calc
      _ = ∫ x in unitCube, (2 : ℝ) *
          ((fourierCharacter k x * z).re * (fourierCharacter l x * w).re) :=
        (integral_const_mul _ _).symm
      _ = ∫ x in unitCube,
          (fourierCharacter (k + l) x * (z * w)).re +
          (fourierCharacter (-k + l) x * (star z * w)).re :=
        integral_congr_ae (Filter.Eventually.of_forall hid)
      _ = (∫ x in unitCube, fourierCharacter (k + l) x * (z * w)).re +
          (∫ x in unitCube, fourierCharacter (-k + l) x * (star z * w)).re := by
        have hr1 : IntegrableOn (fun x : Vec =>
            (fourierCharacter (k + l) x * (z * w)).re) unitCube volume :=
          Complex.reCLM.integrable_comp hfirst
        have hr2 : IntegrableOn (fun x : Vec =>
            (fourierCharacter (-k + l) x * (star z * w)).re) unitCube volume :=
          Complex.reCLM.integrable_comp hsecond
        rw [integral_add hr1 hr2]
        exact congrArg₂ (fun r s : ℝ => r + s)
          (Complex.reCLM.integral_comp_comm hfirst)
          (Complex.reCLM.integral_comp_comm hsecond)
      _ = 0 := by
        rw [integral_mul_const, integral_mul_const,
          integral_fourierCharacter, integral_fourierCharacter]
        simp [hplus, hminus]
  linarith

theorem integral_masked_real_character_product_zero (A B : Fin 6) (hAB : A ≠ B)
    (a b : FourierCoeff) (k l : Frequency) (j : Fin 3) :
    (∫ x in unitCube,
      (fourierCharacter k x * spectralChannel A a k j).re *
      (fourierCharacter l x * spectralChannel B b l j).re) = 0 := by
  by_cases hA : channelOf k j = A
  · by_cases hB : channelOf l j = B
    · apply integral_real_character_product_zero
      · intro h
        have hl : l = -k := by
          calc
            l = -k + (k + l) := by abel
            _ = -k := by rw [h, add_zero]
        apply hAB
        calc
          A = channelOf k j := hA.symm
          _ = channelOf l j := by rw [hl, channelOf_neg]
          _ = B := hB
      · intro h
        have hl : l = k := by
          calc
            l = k + (-k + l) := by abel
            _ = k := by rw [h, add_zero]
        exact hAB (hA.symm.trans (hl ▸ hB))
    · simp [spectralChannel, hB]
  · simp [spectralChannel, hA]

theorem physical_complex_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

theorem integral_unitCube_sum_mul_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → Vec → ℝ) (g : κ → Vec → ℝ)
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

theorem PHYSICAL_CHANNEL_COMPONENT_ORTHOGONALITY (N : ℕ) (A B : Fin 6)
    (hAB : A ≠ B) (a b : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube, physicalChannel N A a x j * physicalChannel N B b x j) = 0 := by
  change (∫ x in unitCube,
    (∑ k ∈ cutoffModes N, fourierCharacter k x * spectralChannel A a k j).re *
    (∑ l ∈ cutoffModes N, fourierCharacter l x * spectralChannel B b l j).re) = 0
  simp_rw [physical_complex_re_sum]
  rw [integral_unitCube_sum_mul_sum _ _ _ _
    (fun k => real_character_continuous k (spectralChannel A a k j))
    (fun l => real_character_continuous l (spectralChannel B b l j))]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  exact integral_masked_real_character_product_zero A B hAB a b k l j

theorem PHYSICAL_CHANNEL_GRADIENT_ORTHOGONALITY (N : ℕ) (A B : Fin 6)
    (hAB : A ≠ B) (a b : FourierCoeff) (i j : Fin 3) :
    (∫ x in unitCube,
      coordinateDerivative (physicalChannel N A a) i x j *
      coordinateDerivative (physicalChannel N B b) i x j) = 0 := by
  simp_rw [physicalChannel_coordinateDerivative]
  exact PHYSICAL_CHANNEL_COMPONENT_ORTHOGONALITY N A B hAB _ _ j

theorem integral_unitCube_square_sum_of_orthogonal (f : Fin 6 → Vec → ℝ)
    (hf : ∀ A, Continuous (f A))
    (horth : ∀ A B, A ≠ B → (∫ x in unitCube, f A x * f B x) = 0) :
    (∫ x in unitCube, (∑ A : Fin 6, f A x) ^ 2) =
      ∑ A : Fin 6, ∫ x in unitCube, (f A x) ^ 2 := by
  simp only [pow_two]
  rw [integral_unitCube_sum_mul_sum Finset.univ Finset.univ f f hf hf]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_eq_single A]
  · intro B _ hBA
    exact horth A B hBA.symm
  · intro hA
    exact (hA (Finset.mem_univ A)).elim

theorem coordinateDerivative_component_continuous {v : Field}
    (hv : ContDiff ℝ ∞ v) (i j : Fin 3) :
    Continuous (fun x : Vec => coordinateDerivative v i x j) :=
  (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp
    (coordinateDerivative_continuous hv i)

set_option maxHeartbeats 1000000 in
theorem integral_gradientSquareDensity {v : Field} (hv : ContDiff ℝ ∞ v) :
    (∫ x in unitCube, gradientSquareDensity v x) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in unitCube, (coordinateDerivative v i x j) ^ 2 := by
  have hcont (i : Fin 3) : Continuous (fun x : Vec =>
      ∑ j : Fin 3, (coordinateDerivative v i x j) ^ 2) :=
    continuous_finsetSum Finset.univ
      (f := fun j x => (coordinateDerivative v i x j) ^ 2)
      (fun j _ => (coordinateDerivative_component_continuous hv i j).pow 2)
  have hint (i : Fin 3) : IntegrableOn (fun x : Vec =>
      ∑ j : Fin 3, (coordinateDerivative v i x j) ^ 2) unitCube volume :=
    (hcont i).continuousOn.integrableOn_compact isCompact_unitCube
  unfold gradientSquareDensity
  rw [integral_finsetSum Finset.univ
    (f := fun i x => ∑ j : Fin 3, (coordinateDerivative v i x j) ^ 2)
    (μ := volume.restrict unitCube) (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum Finset.univ
    (f := fun j x => (coordinateDerivative v i x j) ^ 2)
    (μ := volume.restrict unitCube) (fun j _ =>
    ((coordinateDerivative_component_continuous hv i j).pow 2).continuousOn.integrableOn_compact isCompact_unitCube)

theorem integral_coordinateDerivative_square_sum_channels (N : ℕ) (a : FourierCoeff)
    (i j : Fin 3) :
    (∫ x in unitCube, (coordinateDerivative (finiteSynthesis N a) i x j) ^ 2) =
      ∑ A : Fin 6, ∫ x in unitCube,
        (coordinateDerivative (physicalChannel N A a) i x j) ^ 2 := by
  have hd (x : Vec) : coordinateDerivative (finiteSynthesis N a) i x j =
      ∑ A : Fin 6, coordinateDerivative (physicalChannel N A a) i x j := by
    have hh := congrArg (fun v : Vec => v j)
      (SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION N a i x)
    simpa using hh
  simp_rw [hd]
  exact integral_unitCube_square_sum_of_orthogonal _
    (fun A => coordinateDerivative_component_continuous (physicalChannel_contDiff N A a) i j)
    (fun A B hAB => PHYSICAL_CHANNEL_GRADIENT_ORTHOGONALITY N A B hAB a a i j)

theorem SIX_CHANNEL_FINITE_REAL_ENSTROPHY_EQ (N : ℕ) (a : FourierCoeff) :
    (∫ x in unitCube, gradientSquareDensity (finiteSynthesis N a) x) =
      ∑ A : Fin 6, ∫ x in unitCube, gradientSquareDensity (physicalChannel N A a) x := by
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in unitCube, (coordinateDerivative (finiteSynthesis N a) i x j) ^ 2 :=
      integral_gradientSquareDensity (finiteSynthesis_contDiff N a)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ A : Fin 6,
        ∫ x in unitCube, (coordinateDerivative (physicalChannel N A a) i x j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact integral_coordinateDerivative_square_sum_channels N a i j
    _ = ∑ A : Fin 6, ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in unitCube, (coordinateDerivative (physicalChannel N A a) i x j) ^ 2 := by
      calc
        _ = ∑ i : Fin 3, ∑ A : Fin 6, ∑ j : Fin 3,
            ∫ x in unitCube, (coordinateDerivative (physicalChannel N A a) i x j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      exact (integral_gradientSquareDensity (physicalChannel_contDiff N A a)).symm

theorem physicalEnstrophy_eq_ofReal_integral {v : Field} (hv : ContDiff ℝ ∞ v) :
    physicalEnstrophy v = ENNReal.ofReal (∫ x in unitCube, gradientSquareDensity v x) :=
  (ofReal_integral_eq_lintegral_ofReal (gradientSquareDensity_integrableOn hv)
    (Filter.Eventually.of_forall (gradientSquareDensity_nonneg v))).symm

/-- Exact Pythagoras for all six actual physical gradient integrals of every
finite coefficient family, without a reality or solenoidality assumption. -/
theorem SIX_CHANNEL_FINITE_ENSTROPHY_EQ (N : ℕ) (a : FourierCoeff) :
    sixEnstrophy N a = physicalEnstrophy (finiteSynthesis N a) := by
  change (∑ A : Fin 6, physicalEnstrophy (physicalChannel N A a)) = _
  rw [physicalEnstrophy_eq_ofReal_integral (finiteSynthesis_contDiff N a),
    SIX_CHANNEL_FINITE_REAL_ENSTROPHY_EQ,
    ENNReal.ofReal_sum_of_nonneg (fun A _ =>
      integral_nonneg (gradientSquareDensity_nonneg (physicalChannel N A a)))]
  apply Finset.sum_congr rfl
  intro A _
  exact physicalEnstrophy_eq_ofReal_integral (physicalChannel_contDiff N A a)

theorem SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ (N : ℕ)
    (c : ℝ → FourierCoeff) (T : ℝ) :
    budget6 N c T = ∫⁻ t in Icc (0 : ℝ) T,
      (physicalEnstrophy (finiteSynthesis N (c t))) ^ 2 := by
  simp only [budget6, SIX_CHANNEL_FINITE_ENSTROPHY_EQ]

end

end SingularClosure
