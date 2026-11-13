import FourierHodgeLaws.CosineMultiplier
import NSEMaxwell.FourierPeriodic
import SingularClosure.FiniteHessian

/-! Poisson inversion for the exact cosine vectorL, through actual coefficients. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical

noncomputable section

theorem datumFourierCoeff_add (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    SingularClosure.datumFourierCoeff (a + b) =
      SingularClosure.datumFourierCoeff a + SingularClosure.datumFourierCoeff b := by
  funext k i
  simp only [SingularClosure.datumFourierCoeff, SingularClosure.datumFourierIntegrand,
    Pi.add_apply, PiLp.add_apply, Complex.ofReal_add, mul_add]
  exact integral_add
    (SingularClosure.datumFourierIntegrand_integrableOn ha k i)
    (SingularClosure.datumFourierIntegrand_integrableOn hb k i)

theorem datumFourierCoeff_sub (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    SingularClosure.datumFourierCoeff (a - b) =
      SingularClosure.datumFourierCoeff a - SingularClosure.datumFourierCoeff b := by
  funext k i
  simp only [SingularClosure.datumFourierCoeff, SingularClosure.datumFourierIntegrand,
    Pi.sub_apply, PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  exact integral_sub
    (SingularClosure.datumFourierIntegrand_integrableOn ha k i)
    (SingularClosure.datumFourierIntegrand_integrableOn hb k i)

theorem datumFourierCoeff_neg (a : Field) :
    SingularClosure.datumFourierCoeff (-a) = -SingularClosure.datumFourierCoeff a := by
  funext k i
  simp only [SingularClosure.datumFourierCoeff, SingularClosure.datumFourierIntegrand,
    Pi.neg_apply, PiLp.neg_apply, Complex.ofReal_neg, mul_neg, integral_neg]

theorem datumFourierCoeff_const (m : Vec) :
    SingularClosure.datumFourierCoeff (fun _ : Vec => m) =
      fun k i => if k = 0 then (m i : ℂ) else 0 := by
  funext k i
  change (∫ x in unitCube,
    star (SingularClosure.fourierCharacter k x) * (m i : ℂ)) = _
  simp_rw [← SingularClosure.fourierCharacter_neg]
  rw [integral_mul_const]
  change (∫ x in SingularClosure.unitCube,
    SingularClosure.fourierCharacter (-k) x) * (m i : ℂ) =
      if k = 0 then (m i : ℂ) else 0
  rw [SingularClosure.integral_fourierCharacter]
  by_cases hk : k = 0 <;> simp [hk]

theorem datumFourierCoeff_laplacian (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    SingularClosure.datumFourierCoeff (NSEMaxwell.Classical.laplacian a) =
      SingularClosure.laplacianCoefficient (SingularClosure.datumFourierCoeff a) := by
  let d : Fin 3 → Field := fun j => coordinateDerivative (coordinateDerivative a j) j
  have hd (j : Fin 3) : ContDiff ℝ ∞ (d j) :=
    NSEMaxwell.CurlCurl.coordinateDerivative_smooth
      (NSEMaxwell.CurlCurl.coordinateDerivative_smooth ha j) j
  have ht : NSEMaxwell.Classical.laplacian a = d 0 + d 1 + d 2 := by
    funext x
    change (∑ j : Fin 3, coordinateDerivative (coordinateDerivative a j) j x) = _
    simp [d, Fin.sum_univ_succ, add_assoc]
  rw [ht, datumFourierCoeff_add (d 0 + d 1) (d 2)
      ((hd 0).add (hd 1)).continuous (hd 2).continuous,
    datumFourierCoeff_add (d 0) (d 1) (hd 0).continuous (hd 1).continuous]
  have hdd (j : Fin 3) : SingularClosure.datumFourierCoeff (d j) =
      SingularClosure.spectralMultiplier (SingularClosure.derivativeSymbol j)
        (SingularClosure.spectralMultiplier (SingularClosure.derivativeSymbol j)
          (SingularClosure.datumFourierCoeff a)) := by
    change SingularClosure.datumFourierCoeff
      (coordinateDerivative (coordinateDerivative a j) j) = _
    rw [datumFourierCoeff_coordinateDerivative (coordinateDerivative a j)
      (NSEMaxwell.CurlCurl.coordinateDerivative_smooth ha j)
      (NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic hp j) j,
      datumFourierCoeff_coordinateDerivative a ha hp j]
  rw [hdd 0, hdd 1, hdd 2]
  have h := SingularClosure.sum_double_derivativeMultiplier
    (SingularClosure.datumFourierCoeff a)
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem laplacianFrequency_mul_inverseLaplacianSymbol
    (k : Frequency) (hk : k ≠ 0) :
    SingularClosure.laplacianFrequency k * inverseLaplacianSymbol k = 1 := by
  have hsum : 0 < ∑ j : Fin 3, (k j : ℝ) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    have hi' : (k i : ℝ) ≠ 0 := by
      exact_mod_cast hi
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi')
      (Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i))
  have hf : SingularClosure.laplacianFrequency k =
      4 * Real.pi ^ 2 * (∑ j : Fin 3, (k j : ℝ) ^ 2) := by
    unfold SingularClosure.laplacianFrequency SingularClosure.galerkinFreqSq
    push_cast
    ring
  rw [hf, NSEMaxwell.Classical.inverseLaplacianSymbol, if_neg hk]
  exact mul_inv_cancel₀ (by positivity)

theorem neg_laplacian_vectorL (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    -NSEMaxwell.Classical.laplacian (vectorL a) = a - (fun _ => spatialMean a) := by
  have hL := vectorL_smooth a ha hp
  have hpL := NSEMaxwell.FourierPeriodic.vectorL_periodic a
  have hleft : Continuous (-NSEMaxwell.Classical.laplacian (vectorL a)) :=
    (NSEMaxwell.PeriodicIntegration.laplacian_smooth hL).neg.continuous
  have hright : Continuous (a - (fun _ => spatialMean a)) :=
    ha.continuous.sub continuous_const
  have hpleft : SpatialPeriodic (-NSEMaxwell.Classical.laplacian (vectorL a)) := by
    intro x j
    change -NSEMaxwell.Classical.laplacian (vectorL a) (x + unitVector j) =
      -NSEMaxwell.Classical.laplacian (vectorL a) x
    rw [NSEMaxwell.PeriodicIntegration.laplacian_periodic hpL x j]
  have hpright : SpatialPeriodic (a - (fun _ => spatialMean a)) := by
    intro x j
    change a (x + unitVector j) - spatialMean a = a x - spatialMean a
    rw [hp x j]
  apply SingularClosure.datumFourierCoeff_injective_continuous_periodic _ _
    hleft hright hpleft hpright
  rw [datumFourierCoeff_neg, datumFourierCoeff_laplacian (vectorL a) hL hpL,
    datumFourierCoeff_vectorL a ha hp,
    datumFourierCoeff_sub a (fun _ => spatialMean a) ha.continuous continuous_const,
    datumFourierCoeff_const]
  funext k i
  change -(-(SingularClosure.laplacianFrequency k : ℂ) * inverseVectorCoeff a k i) =
    SingularClosure.datumFourierCoeff a k i -
      (if k = 0 then (spatialMean a i : ℂ) else 0)
  by_cases hk : k = 0
  · subst k
    rw [inverseVectorCoeff_zero]
    simp only [mul_zero, neg_zero, if_pos rfl]
    rw [SingularClosure.datumFourierCoeff_zero
      (NSEMaxwell.PeriodicIntegration.integrableOn_unitCube_of_continuous ha.continuous) i]
    exact (sub_self _).symm
  · rw [if_neg hk, sub_zero]
    have hmul : (SingularClosure.laplacianFrequency k : ℂ) *
        (inverseLaplacianSymbol k : ℂ) = 1 := by
      exact_mod_cast laplacianFrequency_mul_inverseLaplacianSymbol k hk
    unfold inverseVectorCoeff
    calc
      _ = ((SingularClosure.laplacianFrequency k : ℂ) *
          (inverseLaplacianSymbol k : ℂ)) * SingularClosure.datumFourierCoeff a k i := by ring
      _ = _ := by rw [hmul, one_mul]

end

end NSEMaxwell.HodgeProof
