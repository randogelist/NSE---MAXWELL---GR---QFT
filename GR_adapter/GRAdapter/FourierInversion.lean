import GRAdapter.FourierBridge
import GRAdapter.StressDivergence

/-!
# Native Fourier inversion edges from LI03

Every literature assumption is the concrete `LiteratureSmoothFourierInput`.
The coefficients, cube means, cosine integrals, and Laplacian below are the
actual native operators. No operator-inversion law is an input field.
-/

set_option autoImplicit false

namespace NSEGR
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem literatureCharacter_zero (x : Vec) :
    LiteratureCharacter (0 : Frequency) x = 1 := by
  simp [LiteratureCharacter]

theorem literatureFourierCoefficient_zero (f : ScalarField) :
    LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) (0 : Frequency) =
      (scalarMean f : ℂ) := by
  change (∫ y in unitCube, (f y : ℂ) * LiteratureCharacter (0 : Frequency) y) = _
  simp only [literatureCharacter_zero, mul_one]
  exact integral_complex_ofReal

theorem literatureFourier_hasSum_real
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    HasSum (fun k : Frequency =>
      LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k *
        LiteratureCharacter k x) (f x : ℂ) := by
  have hfc : ContDiff ℝ ∞ (fun y : Vec => (f y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hpc : LiteraturePeriodic (fun y : Vec => (f y : ℂ)) := by
    intro y i
    change (f (y + unitVector i) : ℂ) = (f y : ℂ)
    rw [hp y i]
  have hs := (L.reconstruct 3 (by decide) (fun y : Vec => (f y : ℂ)) hfc hpc []).2.2
  simpa [LiteratureFourierWordMultiplier, LiteraturePartialWord] using hs.hasSum (x := x)

theorem literatureFourier_nonzero_hasSum
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    HasSum (fun k : Frequency => if k = 0 then 0 else
      LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k *
        LiteratureCharacter k x) ((f x : ℂ) - (scalarMean f : ℂ)) := by
  classical
  have hs := hasSum_ite_sub_hasSum (literatureFourier_hasSum_real L f hf hp x)
    (0 : Frequency)
  simpa only [literatureFourierCoefficient_zero, literatureCharacter_zero, mul_one] using hs

/-- Native cosine reconstruction with the zero mode removed. -/
theorem cosine_nonzero_hasSum_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    HasSum (fun k : Frequency => if k = 0 then 0 else
      ∫ y in unitCube, cosineKernel k x y * f y) (f x - scalarMean f) := by
  classical
  have hs := Complex.hasSum_re (literatureFourier_nonzero_hasSum L f hf hp x)
  have hterm (k : Frequency) :
      (if k = 0 then (0 : ℂ) else
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k *
          LiteratureCharacter k x).re =
        if k = 0 then 0 else ∫ y in unitCube, cosineKernel k x y * f y := by
    by_cases hk : k = 0
    · simp [hk]
    · simp only [if_neg hk]
      rw [cosineKernel_integral_eq_re_fourier f hf.continuous]
      rw [mul_comm]
  simpa only [hterm, Complex.sub_re, Complex.ofReal_re] using hs

def fourierScalarPartial (f : ScalarField) (i : Fin 3) : ScalarField :=
  fun x => fderiv ℝ f x (unitVector i)

theorem fourierScalarPartial_smooth (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) : ContDiff ℝ ∞ (fourierScalarPartial f i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem fourierScalarPartial_periodic (f : ScalarField) (hp : SpatialPeriodic f)
    (i : Fin 3) : SpatialPeriodic (fourierScalarPartial f i) := by
  intro x j
  exact congrArg (fun D : Vec →L[ℝ] ℝ => D (unitVector i)) (fderiv_periodic hp x j)

theorem scalarLaplacian_smooth (f : ScalarField) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarLaplacian f) := by
  exact ContDiff.sum (fun i _ =>
    fourierScalarPartial_smooth (fourierScalarPartial f i)
      (fourierScalarPartial_smooth f hf i) i)

theorem scalarLaplacian_periodic (f : ScalarField) (hp : SpatialPeriodic f) :
    SpatialPeriodic (scalarLaplacian f) := by
  intro x j
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  exact fourierScalarPartial_periodic (fourierScalarPartial f i)
    (fourierScalarPartial_periodic f hp i) i x j

theorem fourierScalarPartial_ofReal (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (x : Vec) :
    fderiv ℝ (fun y : Vec => (f y : ℂ)) x (unitVector i) =
      (fourierScalarPartial f i x : ℂ) := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x
    ((hf.differentiable (by simp) x).hasFDerivAt)).fderiv
  exact congrArg (fun D : Vec →L[ℝ] ℂ => D (unitVector i)) hd

theorem literaturePartialWord_pair_ofReal (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) :
    LiteraturePartialWord [i,j] (fun y : Vec => (f y : ℂ)) =
      fun x => (fourierScalarPartial (fourierScalarPartial f j) i x : ℂ) := by
  have hfirst : LiteraturePartialWord [j] (fun y : Vec => (f y : ℂ)) =
      fun x => (fourierScalarPartial f j x : ℂ) := by
    funext x
    exact fourierScalarPartial_ofReal f hf j x
  change (fun x => fderiv ℝ
    (LiteraturePartialWord [j] (fun y : Vec => (f y : ℂ))) x (unitVector i)) = _
  rw [hfirst]
  funext x
  exact fourierScalarPartial_ofReal (fourierScalarPartial f j)
    (fourierScalarPartial_smooth f hf j) i x

/-- LI03's differentiated Fourier equality specialized to each actual
second coordinate derivative. -/
theorem literatureFourierCoefficient_secondPartial
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (i : Fin 3) (k : Frequency) :
    LiteratureFourierCoefficient
      (fun y : Vec => (fourierScalarPartial (fourierScalarPartial f i) i y : ℂ)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ 2 *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k := by
  have hfc : ContDiff ℝ ∞ (fun y : Vec => (f y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hpc : LiteraturePeriodic (fun y : Vec => (f y : ℂ)) := by
    intro y j
    change (f (y + unitVector j) : ℂ) = (f y : ℂ)
    rw [hp y j]
  rw [← literaturePartialWord_pair_ofReal f hf i i]
  have h := (L.reconstruct 3 (by decide) (fun y : Vec => (f y : ℂ))
    hfc hpc [i,i]).1 k
  simpa [LiteratureFourierWordMultiplier, pow_two] using h

/-- The exact native scalar Laplacian has the expected negative Fourier
multiplier under LI03; no Laplacian inversion law is assumed. -/
theorem literatureFourierCoefficient_scalarLaplacian
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (k : Frequency) :
    LiteratureFourierCoefficient (fun y : Vec => (scalarLaplacian f y : ℂ)) k =
      ((-(4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) : ℝ) : ℂ) *
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k := by
  have hsum : LiteratureFourierCoefficient (fun y : Vec => (scalarLaplacian f y : ℂ)) k =
      ∑ i : Fin 3, LiteratureFourierCoefficient
        (fun y : Vec => (fourierScalarPartial (fourierScalarPartial f i) i y : ℂ)) k := by
    unfold LiteratureFourierCoefficient
    change (∫ y in unitCube, (scalarLaplacian f y : ℂ) * LiteratureCharacter (-k) y) = _
    have heq (y : Vec) : (scalarLaplacian f y : ℂ) =
        ∑ i : Fin 3, (fourierScalarPartial (fourierScalarPartial f i) i y : ℂ) := by
      simp [scalarLaplacian, fourierScalarPartial]
    simp_rw [heq, Finset.sum_mul]
    apply integral_finsetSum
    intro i _
    exact integrableOn_unitCube_of_continuous
      ((Complex.continuous_ofReal.comp
        (fourierScalarPartial_smooth (fourierScalarPartial f i)
          (fourierScalarPartial_smooth f hf i) i).continuous).mul
        (literatureCharacter_continuous (-k)))
  rw [hsum]
  simp_rw [literatureFourierCoefficient_secondPartial L f hf hp]
  rw [← Finset.sum_mul]
  congr 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  push_cast
  simp only [mul_pow, Complex.I_sq]
  ring

theorem poissonSymbol_mul_scalarLaplacianSymbol (k : Frequency) :
    poissonSymbol k * (-(4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2)) =
      if k = 0 then 0 else 1 := by
  by_cases hk : k = 0
  · simp [hk, poissonSymbol]
  · have hsum : 0 < ∑ i : Fin 3, (k i : ℝ) ^ 2 :=
      zero_lt_one.trans_le (frequency_square_sum_ge_one k hk)
    have hden : 4 * Real.pi ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) ≠ 0 := by positivity
    simp [poissonSymbol, hk, hden]

/-- One native inverse direction: G(Delta f)=f-mean(f), derived from LI03
for every smooth periodic real field, with no additional analytic law. -/
theorem poissonInverse_scalarLaplacian_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (x : Vec) :
    poissonInverse (scalarLaplacian f) x = f x - scalarMean f := by
  classical
  rw [poissonInverse_eq_re_tsum_fourier_of_literature L (scalarLaplacian f)
    (scalarLaplacian_smooth f hf) (scalarLaplacian_periodic f hp)]
  have hterm (k : Frequency) :
      (poissonSymbol k : ℂ) * (LiteratureCharacter k x *
        LiteratureFourierCoefficient (fun y : Vec => (scalarLaplacian f y : ℂ)) k) =
      if k = 0 then 0 else
        LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k *
          LiteratureCharacter k x := by
    rw [literatureFourierCoefficient_scalarLaplacian L f hf hp]
    have hprod := congrArg (fun r : ℝ => (r : ℂ))
      (poissonSymbol_mul_scalarLaplacianSymbol k)
    rw [Complex.ofReal_mul] at hprod
    calc
      _ = ((poissonSymbol k : ℂ) *
          ((-(4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) : ℝ) : ℂ)) *
          (LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k *
            LiteratureCharacter k x) := by ring
      _ = _ := by
        rw [hprod]
        split_ifs <;> simp
  simp_rw [hterm]
  rw [(literatureFourier_nonzero_hasSum L f hf hp x).tsum_eq]
  simp

theorem gradient_sub_constant (f : ScalarField) (c : ℝ) :
    gradient (fun x => f x - c) = gradient f := by
  funext x
  simp only [gradient, fderiv_sub_const]

/-- The native Leray formula annihilates every smooth periodic gradient.
The sole analytic input is LI03; the divergence-gradient identity is native. -/
theorem leray_gradient_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    leray (gradient f) = 0 := by
  have hG : poissonInverse (scalarLaplacian f) = fun x => f x - scalarMean f :=
    funext (poissonInverse_scalarLaplacian_of_literature L f hf hp)
  funext x
  change gradient f x - gradient (poissonInverse (divergence (gradient f))) x = 0
  rw [divergence_gradient hf, hG, gradient_sub_constant, sub_self]

end
end NSEGR
