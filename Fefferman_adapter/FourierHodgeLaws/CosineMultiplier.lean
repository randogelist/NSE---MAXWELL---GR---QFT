import FourierHodgeLaws.FourierCoefficients
import NSEMaxwell.PeriodicIntegration
import SingularClosure.PeriodicFourierInjective

/-! Identification of the frozen full-lattice cosine operator with native synthesis. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical

noncomputable section

theorem fourierCharacter_mul_star (k : Frequency) (x y : Vec) :
    SingularClosure.fourierCharacter k x * star (SingularClosure.fourierCharacter k y) =
      Complex.exp (((2 * Real.pi *
        (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) : ℝ) : ℂ) * Complex.I) := by
  rw [← SingularClosure.fourierCharacter_neg]
  simp only [SingularClosure.fourierCharacter, Pi.neg_apply, Int.cast_neg, neg_mul,
    Finset.sum_neg_distrib, mul_neg, Complex.ofReal_neg, neg_mul]
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

theorem cosineKernel_eq_character_re (k : Frequency) (x y : Vec) :
    cosineKernel k x y =
      (SingularClosure.fourierCharacter k x *
        star (SingularClosure.fourierCharacter k y)).re := by
  rw [fourierCharacter_mul_star, Complex.exp_ofReal_mul_I_re]
  rfl

theorem scalar_cosine_integral (f : ScalarField) (hf : Continuous f)
    (k : Frequency) (x : Vec) :
    (∫ y in unitCube, cosineKernel k x y * f y) =
      (SingularClosure.fourierCharacter k x * scalarCoeff f k).re := by
  have hint : IntegrableOn
      (fun y : Vec => SingularClosure.fourierCharacter k x *
        (star (SingularClosure.fourierCharacter k y) * (f y : ℂ))) unitCube volume :=
    (continuous_const.mul ((SingularClosure.fourierCharacter_contDiff k).continuous.star.mul
      (Complex.continuous_ofReal.comp hf))).continuousOn.integrableOn_compact
        NSEMaxwell.PeriodicIntegration.isCompact_unitCube
  calc
    _ = ∫ y in unitCube,
        (SingularClosure.fourierCharacter k x *
          (star (SingularClosure.fourierCharacter k y) * (f y : ℂ))).re := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only
        rw [cosineKernel_eq_character_re]
        simp only [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero])
    _ = (∫ y in unitCube, SingularClosure.fourierCharacter k x *
          (star (SingularClosure.fourierCharacter k y) * (f y : ℂ))).re :=
      Complex.reCLM.integral_comp_comm hint
    _ = _ := by rw [integral_const_mul]; rfl

theorem scalar_cosine_summand (f : ScalarField) (hf : Continuous f)
    (k : Frequency) (x : Vec) :
    inverseLaplacianSymbol k * (∫ y in unitCube, cosineKernel k x y * f y) =
      (SingularClosure.fourierCharacter k x * inverseScalarCoeff f k).re := by
  rw [scalar_cosine_integral f hf]
  unfold inverseScalarCoeff
  rw [mul_left_comm]
  simp [Complex.mul_re]

theorem scalarL_eq_realFourierSeries (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    scalarL f = SingularClosure.realFourierSeries (inverseScalarCoeff f) := by
  funext x
  have hs := SingularClosure.scalarFourierSeries_summable
    (rapid_inverseScalarCoeff f hf hp).summable_norm x
  have hre := Complex.reCLM.map_tsum hs
  simp only [Complex.reCLM_apply] at hre
  unfold scalarL SingularClosure.realFourierSeries SingularClosure.scalarFourierSeries
  rw [hre]
  apply tsum_congr
  intro k
  exact scalar_cosine_summand f hf.continuous k x

theorem vector_cosine_integral_component (F : Field) (hF : Continuous F)
    (k : Frequency) (x : Vec) (i : Fin 3) :
    (∫ y in unitCube, cosineKernel k x y • F y) i =
      ∫ y in unitCube, cosineKernel k x y * F y i := by
  have hc : Continuous (fun y : Vec => cosineKernel k x y) := by
    unfold cosineKernel
    fun_prop
  have hi : IntegrableOn (fun y : Vec => cosineKernel k x y • F y) unitCube volume :=
    (hc.smul hF).continuousOn.integrableOn_compact
      NSEMaxwell.PeriodicIntegration.isCompact_unitCube
  have h := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).integral_comp_comm hi
  simpa only [EuclideanSpace.coe_proj, PiLp.smul_apply, smul_eq_mul] using h.symm

theorem vector_cosine_summand_component (F : Field) (hF : Continuous F)
    (k : Frequency) (x : Vec) (i : Fin 3) :
    (inverseLaplacianSymbol k •
      (∫ y in unitCube, cosineKernel k x y • F y)) i =
      (SingularClosure.fourierCharacter k x * inverseVectorCoeff F k i).re := by
  change inverseLaplacianSymbol k *
    (∫ y in unitCube, cosineKernel k x y • F y) i = _
  rw [vector_cosine_integral_component F hF]
  exact scalar_cosine_summand (fun y => F y i)
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp hF) k x

theorem vectorL_summable (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) (x : Vec) :
    Summable (fun k : Frequency => inverseLaplacianSymbol k •
      (∫ y in unitCube, cosineKernel k x y • F y)) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).summable.mp
  apply Pi.summable.mpr
  intro i
  have hs := (SingularClosure.scalarFourierSeries_summable
    (rapid_inverseLaplacianCoeff F hF hp i).summable_norm x).mapL Complex.reCLM
  simp only [Complex.reCLM_apply] at hs
  exact hs.congr (fun k => (vector_cosine_summand_component F hF.continuous k x i).symm)

theorem vectorL_eq_smoothFourierSynthesis (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) :
    vectorL F = SingularClosure.smoothFourierSynthesis (inverseVectorCoeff F) := by
  funext x
  ext i
  have hpj := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).map_tsum
    (vectorL_summable F hF hp x)
  simp only [EuclideanSpace.coe_proj] at hpj
  change (∑' k : Frequency, inverseLaplacianSymbol k •
    (∫ y in unitCube, cosineKernel k x y • F y)) i = _
  rw [hpj]
  change (∑' k : Frequency, (inverseLaplacianSymbol k •
    (∫ y in unitCube, cosineKernel k x y • F y)) i) =
      (∑' k : Frequency, SingularClosure.fourierCharacter k x * inverseVectorCoeff F k i).re
  have hre := Complex.reCLM.map_tsum (SingularClosure.scalarFourierSeries_summable
    (rapid_inverseLaplacianCoeff F hF hp i).summable_norm x)
  simp only [Complex.reCLM_apply] at hre
  rw [hre]
  apply tsum_congr
  intro k
  exact vector_cosine_summand_component F hF.continuous k x i

theorem vectorL_smooth (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) : ContDiff ℝ ∞ (vectorL F) := by
  rw [vectorL_eq_smoothFourierSynthesis F hF hp]
  exact SingularClosure.smoothFourierSynthesis_contDiff _
    (rapid_inverseLaplacianCoeff F hF hp)

theorem datumFourierCoeff_vectorL (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) :
    SingularClosure.datumFourierCoeff (vectorL F) = inverseVectorCoeff F := by
  rw [vectorL_eq_smoothFourierSynthesis F hF hp]
  exact SingularClosure.datumFourierCoeff_smoothFourierSynthesis _
    (rapid_inverseLaplacianCoeff F hF hp) (inverseVectorCoeff_reality F)

theorem scalarL_smooth (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) : ContDiff ℝ ∞ (scalarL f) := by
  rw [scalarL_eq_realFourierSeries f hf hp]
  exact SingularClosure.realFourierSeries_contDiff (rapid_inverseScalarCoeff f hf hp)

theorem vectorL_component (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) (i : Fin 3) :
    (fun x => vectorL F x i) = scalarL (fun x => F x i) := by
  have hfi : ContDiff ℝ ∞ (fun x => F x i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hF
  have hpi : SpatialPeriodic (fun x => F x i) := fun x j => congrArg (fun v : Vec => v i) (hp x j)
  rw [vectorL_eq_smoothFourierSynthesis F hF hp,
    scalarL_eq_realFourierSeries (fun x => F x i) hfi hpi]
  rfl

@[simp]
theorem scalarL_zero : scalarL (0 : ScalarField) = 0 := by
  funext x
  simp [scalarL]

@[simp]
theorem vectorL_zero : vectorL (0 : Field) = 0 := by
  funext x
  simp [vectorL]

end

end NSEMaxwell.HodgeProof
