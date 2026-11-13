import QuantumAdapter.Obligations.EnergyFourier
import QuantumAdapter.Obligations.EnergyBilinear

/-! Exact mixed physical transport and its coefficient pairing. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

/-- Advection of the second field by the first. -/
def mixedConvection (a b : Field) : Field :=
  fun x => fderiv ℝ b x (a x)

theorem mixedConvection_self (a : Field) : mixedConvection a a = convection a := rfl

theorem mixedConvection_eq_sum (a b : Field) (x : Vec) :
    mixedConvection a b x = ∑ j : Fin 3, a x j • coordinateDerivative b j x := by
  have hx : (∑ j : Fin 3, a x j • unitVector j) = a x := by
    ext i
    fin_cases i <;> simp [unitVector, Fin.sum_univ_succ, Pi.single_apply]
  have h := congrArg (fderiv ℝ b x) hx
  simpa only [map_sum, map_smul, mixedConvection, coordinateDerivative] using h.symm

theorem mixedConvection_component_eq_sum (a b : Field) (x : Vec) (i : Fin 3) :
    mixedConvection a b x i =
      ∑ j : Fin 3, a x j * coordinateDerivative b j x i := by
  have h := congrArg (EuclideanSpace.proj i : Vec →L[ℝ] ℝ)
    (mixedConvection_eq_sum a b x)
  simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.coe_proj] using h

theorem mixedConvection_continuous (a b : Field)
    (ha : Continuous a) (hb : ContDiff ℝ ∞ b) :
    Continuous (mixedConvection a b) :=
  (hb.continuous_fderiv (by simp)).clm_apply ha

theorem datumFourierCoeff_mixedConvection_fullSynthesis
    (N : ℕ) (a b : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ fullModes N → ∀ i : Fin 3, b k i = 0)
    (ha : SpectralReality a) (hb : SpectralReality b) :
    datumFourierCoeff (mixedConvection (fullSynthesis N a) (fullSynthesis N b)) =
      fullBilinearTransport N a b := by
  funext k i
  have hpoint (x : Vec) :
      (mixedConvection (fullSynthesis N a) (fullSynthesis N b) x i : ℂ) =
        ∑ j : Fin 3, complexFullSynthesis N a j x *
          complexFullSynthesis N (spectralMultiplier (derivativeSymbol j) b) i x := by
    rw [mixedConvection_component_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [fullSynthesis_coordinateDerivative,
      complexFullSynthesis_eq_ofReal N a ha,
      complexFullSynthesis_eq_ofReal N _ (derivativeMultiplier_reality b hb j)]
    all_goals rfl
  unfold datumFourierCoeff datumFourierIntegrand
  simp_rw [hpoint, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => star (fourierCharacter k x) *
      (complexFullSynthesis N a j x *
        complexFullSynthesis N (spectralMultiplier (derivativeSymbol j) b) i x))
    (μ := volume.restrict unitCube) (fun j hj =>
      ((fourierCharacter_contDiff k).continuous.star.mul
        ((complexFullSynthesis_continuous N a j).mul
          (complexFullSynthesis_continuous N _ i))).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  have hmul (j : Fin 3) : ∀ k : Frequency, k ∉ fullModes N → ∀ i : Fin 3,
      spectralMultiplier (derivativeSymbol j) b k i = 0 := by
    intro k hk i
    simp [spectralMultiplier, hsupp k hk i]
  have hterm (j : Fin 3) := integral_complexFullSynthesis_product_coefficient N a
    (spectralMultiplier (derivativeSymbol j) b) (hmul j) k j i
  simp_rw [hterm]
  rw [Finset.sum_comm]
  unfold fullBilinearTransport
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [spectralMultiplier]
  ring

theorem integral_synthesis_mixedConvection (N : ℕ) (q a b : Phase N) :
    (∫ x in unitCube, inner ℝ (synthesis q x)
      (mixedConvection (synthesis a) (synthesis b) x)) =
        ∑ k ∈ fullModes N, ∑ i : Fin 3,
          (star (phaseCoeff q k i) *
            fullBilinearTransport N (phaseCoeff a) (phaseCoeff b) k i).re := by
  change (∫ x in unitCube, inner ℝ (fullSynthesis N (phaseCoeff q) x)
    (mixedConvection (fullSynthesis N (phaseCoeff a))
      (fullSynthesis N (phaseCoeff b)) x)) = _
  rw [integral_fullSynthesis_pairing N (phaseCoeff q) _
    (mixedConvection_continuous _ _ (fullSynthesis_contDiff N _).continuous
      (fullSynthesis_contDiff N _)),
    datumFourierCoeff_mixedConvection_fullSynthesis N _ _ (phaseCoeff_support b)
      (phaseCoeff_reality a) (phaseCoeff_reality b)]

theorem integral_synthesis_transport_zero (N : ℕ) (a b : Phase N) :
    (∫ x in unitCube, inner ℝ (synthesis b x)
      (mixedConvection (synthesis a) (synthesis b) x)) = 0 := by
  rw [integral_synthesis_mixedConvection]
  simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re
    (fullBilinearTransport_energy_zero N (phaseCoeff a) (phaseCoeff b)
      (phaseCoeff_support b) (phaseCoeff_reality b) (phaseCoeff_solenoidal a))

/-- The physical Frobenius gradient controls every directional derivative,
with exact coefficient one. -/
theorem synthesis_directionalDerivative_norm_le (N : ℕ) (q : Phase N)
    (x v : Vec) :
    ‖fderiv ℝ (synthesis q) x v‖ ≤ gradientObservable q * ‖v‖ := by
  let d : Fin 3 → Vec := fun j => coordinateDerivative (synthesis q) j x
  let S : ℝ := ∑ j : Fin 3, |v j| * ‖d j‖
  have hv : (∑ j : Fin 3, v j • unitVector j) = v := by
    ext i
    fin_cases i <;> simp [unitVector, Fin.sum_univ_succ, Pi.single_apply]
  have he : fderiv ℝ (synthesis q) x v = ∑ j : Fin 3, v j • d j := by
    have hh := congrArg (fderiv ℝ (synthesis q) x) hv
    simpa only [map_sum, map_smul, d, coordinateDerivative] using hh.symm
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j hj =>
    mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hnorm : ‖fderiv ℝ (synthesis q) x v‖ ≤ S := by
    rw [he]
    calc
      _ ≤ ∑ j : Fin 3, ‖v j • d j‖ := norm_sum_le _ _
      _ = S := by simp only [S, norm_smul, Real.norm_eq_abs]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin 3 => |v j|) (fun j => ‖d j‖)
  have hvs : (∑ j : Fin 3, |v j|^2) = ‖v‖^2 := by
    simp only [sq_abs, EuclideanSpace.real_norm_sq_eq]
  have hds : (∑ j : Fin 3, ‖d j‖^2) = gradientSquare q x := rfl
  change S^2 ≤ (∑ j : Fin 3, |v j|^2) * (∑ j : Fin 3, ‖d j‖^2) at hCS
  rw [hvs, hds] at hCS
  have hG := Assembly.gradientObservable_nonneg N q
  have hg : Real.sqrt (gradientSquare q x) ≤ gradientObservable q :=
    le_csSup (Assembly.gradientObservable_range_bddAbove N q) (Set.mem_range_self x)
  have hgs := Real.sq_sqrt (Assembly.gradientSquare_nonneg N q x)
  have hg0 := Real.sqrt_nonneg (gradientSquare q x)
  have hGsq : gradientSquare q x ≤ gradientObservable q ^ 2 := by
    have hh := pow_le_pow_left₀ hg0 hg 2
    rwa [hgs] at hh
  have hbound : S^2 ≤ (gradientObservable q * ‖v‖)^2 := by
    have hmul := mul_le_mul_of_nonneg_left hGsq (sq_nonneg ‖v‖)
    nlinarith
  have hr0 := mul_nonneg hG (norm_nonneg v)
  exact hnorm.trans ((sq_le_sq₀ hS hr0).mp hbound)

theorem synthesis_relative_transport_pointwise (N : ℕ) (q r : Phase N) (x : Vec) :
    -inner ℝ (synthesis q x)
      (mixedConvection (synthesis q) (synthesis r) x) ≤
        gradientObservable r * ‖synthesis q x‖^2 := by
  have h := abs_real_inner_le_norm (synthesis q x)
    (mixedConvection (synthesis q) (synthesis r) x)
  have hd := synthesis_directionalDerivative_norm_le N r x (synthesis q x)
  change ‖mixedConvection (synthesis q) (synthesis r) x‖ ≤ _ at hd
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg (synthesis q x))
  have hi := neg_le_abs (inner ℝ (synthesis q x)
    (mixedConvection (synthesis q) (synthesis r) x))
  nlinarith

theorem synthesis_relative_transport_integral (N : ℕ) (q r : Phase N) :
    -(∫ x in unitCube, inner ℝ (synthesis q x)
      (mixedConvection (synthesis q) (synthesis r) x)) ≤
        gradientObservable r * ‖q‖^2 := by
  have hq := (synthesis_contDiff N q).continuous
  have hm := mixedConvection_continuous _ _ hq (synthesis_contDiff N r)
  have hi : IntegrableOn (fun x => inner ℝ (synthesis q x)
      (mixedConvection (synthesis q) (synthesis r) x)) unitCube :=
    (hq.inner hm).continuousOn.integrableOn_compact isCompact_unitCube
  have he : IntegrableOn (fun x => ‖synthesis q x‖^2) unitCube :=
    (hq.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have h := integral_mono hi.neg (he.const_mul (gradientObservable r))
    (fun x => synthesis_relative_transport_pointwise N q r x)
  simp only [Pi.neg_apply] at h
  rw [integral_neg, integral_const_mul, integral_synthesis_norm_sq] at h
  exact h

theorem synthesis_gradientSquare_continuous (N : ℕ) (q : Phase N) :
    Continuous (gradientSquare q) := by
  unfold gradientSquare
  exact continuous_finsetSum _ (fun j hj =>
    ((coordinateDerivative_continuous (synthesis_contDiff N q) j).norm.pow 2))

theorem synthesis_directionalDerivative_norm_le_pointwise (N : ℕ) (q : Phase N)
    (x v : Vec) :
    ‖fderiv ℝ (synthesis q) x v‖ ≤ Real.sqrt (gradientSquare q x) * ‖v‖ := by
  let d : Fin 3 → Vec := fun j => coordinateDerivative (synthesis q) j x
  let S : ℝ := ∑ j : Fin 3, |v j| * ‖d j‖
  have hv : (∑ j : Fin 3, v j • unitVector j) = v := by
    ext i
    fin_cases i <;> simp [unitVector, Fin.sum_univ_succ, Pi.single_apply]
  have he : fderiv ℝ (synthesis q) x v = ∑ j : Fin 3, v j • d j := by
    have hh := congrArg (fderiv ℝ (synthesis q) x) hv
    simpa only [map_sum, map_smul, d, coordinateDerivative] using hh.symm
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j hj =>
    mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hn : ‖fderiv ℝ (synthesis q) x v‖ ≤ S := by
    rw [he]
    calc
      _ ≤ ∑ j : Fin 3, ‖v j • d j‖ := norm_sum_le _ _
      _ = S := by simp only [S, norm_smul, Real.norm_eq_abs]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin 3 => |v j|) (fun j => ‖d j‖)
  have hvs : (∑ j : Fin 3, |v j|^2) = ‖v‖^2 := by
    simp only [sq_abs, EuclideanSpace.real_norm_sq_eq]
  have hds : (∑ j : Fin 3, ‖d j‖^2) = gradientSquare q x := rfl
  change S^2 ≤ (∑ j : Fin 3, |v j|^2) * (∑ j : Fin 3, ‖d j‖^2) at hCS
  rw [hvs, hds] at hCS
  have hs : S^2 ≤ (Real.sqrt (gradientSquare q x) * ‖v‖)^2 := by
    rw [mul_pow, Real.sq_sqrt (Assembly.gradientSquare_nonneg N q x)]
    simpa only [mul_comm] using hCS
  exact hn.trans ((sq_le_sq₀ hS
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs)

end
end QuantumAdapter.Obligations
