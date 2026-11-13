import SingularClosure.PhysicalBilinear
import SingularClosure.InitialFourier

/-!
# Uniform initial Fourier cutoff bounds

The bounds use finite orthogonality and periodic integration by parts on the
actual physical cube. No infinite Fourier completeness theorem is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem FINITE_PHYSICAL_BESSEL (N : ℕ) (a : Field) (ha : Continuous a)
    (hreal : SpectralReality (datumFourierCoeff a)) :
    coefficientEnergy N (datumFourierCoeff a) ≤ physicalEnergy a := by
  let u : Field := finiteSynthesis N (datumFourierCoeff a)
  have hu : Continuous u := (finiteSynthesis_contDiff N _).continuous
  have hi : IntegrableOn (fun x : Vec => inner ℝ (a x) (u x)) unitCube volume :=
    (ha.inner hu).continuousOn.integrableOn_compact isCompact_unitCube
  have ha2 : IntegrableOn (fun x : Vec => ‖a x‖ ^ 2) unitCube volume :=
    (ha.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hu2 : IntegrableOn (fun x : Vec => ‖u x‖ ^ 2) unitCube volume :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have he : (∫ x in unitCube, ‖u x‖ ^ 2) = coefficientEnergy N (datumFourierCoeff a) := by
    rw [← physicalEnergy_eq_integral_norm_sq]
    exact FINITE_PHYSICAL_ENERGY_PARSEVAL N _ hreal
  have hp : (∫ x in unitCube, inner ℝ (a x) (u x)) =
      coefficientEnergy N (datumFourierCoeff a) := by
    have hswap (x : Vec) : inner ℝ (a x) (u x) = inner ℝ (u x) (a x) :=
      real_inner_comm _ _
    simp_rw [hswap]
    rw [integral_finiteSynthesis_pairing N (datumFourierCoeff a) a ha]
    unfold coefficientEnergy
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    all_goals rfl
  have hres : (∫ x in unitCube, ‖a x - u x‖ ^ 2) =
      physicalEnergy a - coefficientEnergy N (datumFourierCoeff a) := by
    simp_rw [norm_sub_sq_real]
    have hleft : IntegrableOn
        (fun x : Vec => ‖a x‖ ^ 2 - 2 * inner ℝ (a x) (u x)) unitCube volume :=
      ha2.sub (hi.const_mul 2)
    rw [integral_add hleft hu2,
      integral_sub ha2 (hi.const_mul 2), integral_const_mul, hp, he,
      ← physicalEnergy_eq_integral_norm_sq]
    ring
  have hnonneg : 0 ≤ ∫ x in unitCube, ‖a x - u x‖ ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [hres] at hnonneg
  linarith

/-- The finite Bessel bound for the actual coefficients of any continuous real field. -/
theorem coefficientEnergy_initial_cutoff_le (N : ℕ) (a : Field)
    (ha : Continuous a) :
    coefficientEnergy N (datumFourierCoeff a) ≤ physicalEnergy a :=
  FINITE_PHYSICAL_BESSEL N a ha (datumFourierCoeff_reality a)

/-- A single periodic directional derivative has zero integral on the physical cube. -/
theorem integral_unitCube_directionalDerivative_eq_zero (f : Vec → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) :
    (∫ x in unitCube, fderiv ℝ f x (unitVector j)) = 0 := by
  classical
  let F : Fin 3 → Vec → ℂ := fun l => if l = j then f else fun _ => 0
  have hF : ∀ l, ContDiff ℝ ∞ (F l) := by
    intro l
    by_cases hl : l = j
    · simpa [F, hl] using hf
    · simpa [F, hl] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Vec => (0 : ℂ)))
  have hperiod : ∀ l x, F l (x + unitVector l) = F l x := by
    intro l x
    by_cases hl : l = j
    · subst l
      simpa [F] using hp x j
    · simp [F, hl]
  have hsum (x : Vec) : (∑ l : Fin 3, fderiv ℝ (F l) x (unitVector l)) =
      fderiv ℝ f x (unitVector j) := by
    have hterm (l : Fin 3) : fderiv ℝ (F l) x (unitVector l) =
        if l = j then fderiv ℝ f x (unitVector j) else 0 := by
      by_cases hl : l = j
      · subst l
        simp [F]
      · simp [F, hl]
    simp_rw [hterm]
    simp
  have h := integral_unitCube_divergence_eq_zero F hF hperiod
  simpa only [hsum] using h

set_option backward.isDefEq.respectTransparency false in
/-- Integration-by-parts integrand identity, with independent component and direction. -/
theorem datumFourierIntegrand_directionalDerivative {a : Field}
    (ha : Differentiable ℝ a) (k : Frequency) (i j : Fin 3) (x : Vec) :
    fderiv ℝ (datumFourierIntegrand a k i) x (unitVector j) =
      star (fourierCharacter k x) * (coordinateDerivative a j x i : ℂ) -
        derivativeSymbol j k * datumFourierIntegrand a k i x := by
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

/-- The actual Fourier coefficients of a classical periodic derivative. -/
theorem datumFourierCoeff_coordinateDerivative (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    datumFourierCoeff (coordinateDerivative a j) =
      spectralMultiplier (derivativeSymbol j) (datumFourierCoeff a) := by
  funext k i
  have hzero := integral_unitCube_directionalDerivative_eq_zero
    (datumFourierIntegrand a k i) (datumFourierIntegrand_contDiff ha k i)
    (datumFourierIntegrand_periodic hp k i) j
  simp_rw [datumFourierIntegrand_directionalDerivative (ha.differentiable (by simp))]
    at hzero
  change (∫ x in unitCube,
    datumFourierIntegrand (coordinateDerivative a j) k i x -
      derivativeSymbol j k * datumFourierIntegrand a k i x) = 0 at hzero
  have hd := datumFourierIntegrand_integrableOn (coordinateDerivative_continuous ha j) k i
  have hv := (datumFourierIntegrand_integrableOn ha.continuous k i).const_mul
    (derivativeSymbol j k)
  rw [integral_sub hd hv, integral_const_mul] at hzero
  exact sub_eq_zero.mp hzero

theorem integral_gradientSquareDensity_eq_sum_physicalEnergy (a : Field)
    (ha : ContDiff ℝ ∞ a) :
    (∫ x in unitCube, gradientSquareDensity a x) =
      ∑ j : Fin 3, physicalEnergy (coordinateDerivative a j) := by
  simp_rw [gradientSquareDensity_eq_sum_norm_sq, physicalEnergy_eq_integral_norm_sq]
  exact integral_finsetSum Finset.univ (fun j _ =>
    ((coordinateDerivative_continuous ha j).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube)

/-- Uniform H¹ seminorm contraction of the actual initial Fourier cutoff. -/
theorem coefficientDissipation_initial_cutoff_le (N : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coefficientDissipation N (datumFourierCoeff a) ≤
      ∫ x in unitCube, gradientSquareDensity a x := by
  have hcomm (j : Fin 3) :
      coordinateDerivative (finiteSynthesis N (datumFourierCoeff a)) j =
        finiteSynthesis N (datumFourierCoeff (coordinateDerivative a j)) := by
    rw [finiteSynthesis_coordinateDerivative, datumFourierCoeff_coordinateDerivative j a ha hp]
  calc
    _ = ∫ x in unitCube,
        gradientSquareDensity (finiteSynthesis N (datumFourierCoeff a)) x :=
      (FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N _ (datumFourierCoeff_reality a)).symm
    _ = ∑ j : Fin 3,
        physicalEnergy (coordinateDerivative (finiteSynthesis N (datumFourierCoeff a)) j) :=
      integral_gradientSquareDensity_eq_sum_physicalEnergy _ (finiteSynthesis_contDiff N _)
    _ = ∑ j : Fin 3,
        physicalEnergy (finiteSynthesis N (datumFourierCoeff (coordinateDerivative a j))) := by
      simp_rw [hcomm]
    _ = ∑ j : Fin 3, coefficientEnergy N (datumFourierCoeff (coordinateDerivative a j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact FINITE_PHYSICAL_ENERGY_PARSEVAL N _ (datumFourierCoeff_reality _)
    _ ≤ ∑ j : Fin 3, physicalEnergy (coordinateDerivative a j) := by
      apply Finset.sum_le_sum
      intro j _
      exact coefficientEnergy_initial_cutoff_le N _ (coordinateDerivative_continuous ha j)
    _ = ∫ x in unitCube, gradientSquareDensity a x :=
      (integral_gradientSquareDensity_eq_sum_physicalEnergy a ha).symm

theorem GalerkinSolution.coefficientDissipation_initial_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    coefficientDissipation N (g.coeff 0) = coefficientDissipation N (datumFourierCoeff a) := by
  unfold coefficientDissipation
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i _
  rw [g.initial k i, if_pos hk]

/-- Initial Galerkin enstrophy is bounded by the datum independently of N. -/
theorem GalerkinSolution.coefficientDissipation_initial_le
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (ha : SmoothSigmaZero a) :
    coefficientDissipation N (g.coeff 0) ≤ ∫ x in unitCube, gradientSquareDensity a x := by
  rw [g.coefficientDissipation_initial_eq]
  exact coefficientDissipation_initial_cutoff_le N a ha.smooth ha.periodic

end

end SingularClosure
