import QuantumAdapter.Obligations.TensorInterpolation
import SingularClosure.FiniteHessian

/-! Static Fourier identities for the actual smooth periodic PDE operators. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem datumFourierCoeff_add (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a + b) = datumFourierCoeff a + datumFourierCoeff b := by
  funext k i
  have hp (x : Vec) : datumFourierIntegrand (a + b) k i x =
      datumFourierIntegrand a k i x + datumFourierIntegrand b k i x := by
    change star (fourierCharacter k x) * ((a x i + b x i : ℝ) : ℂ) = _
    simp only [datumFourierIntegrand, Complex.ofReal_add, mul_add]
  simp only [datumFourierCoeff, hp, Pi.add_apply]
  exact integral_add (datumFourierIntegrand_integrableOn ha k i)
    (datumFourierIntegrand_integrableOn hb k i)

theorem datumFourierCoeff_sub (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a - b) = datumFourierCoeff a - datumFourierCoeff b := by
  funext k i
  have hp (x : Vec) : datumFourierIntegrand (a - b) k i x =
      datumFourierIntegrand a k i x - datumFourierIntegrand b k i x := by
    change star (fourierCharacter k x) * ((a x i - b x i : ℝ) : ℂ) = _
    simp only [datumFourierIntegrand, Complex.ofReal_sub, mul_sub]
  simp only [datumFourierCoeff, hp, Pi.sub_apply]
  exact integral_sub (datumFourierIntegrand_integrableOn ha k i)
    (datumFourierIntegrand_integrableOn hb k i)

theorem datumFourierCoeff_real_smul (a : Field) (r : ℝ) :
    datumFourierCoeff (r • a) = r • datumFourierCoeff a := by
  funext k i
  have hp (x : Vec) : datumFourierIntegrand (r • a) k i x =
      (r : ℂ) * datumFourierIntegrand a k i x := by
    change star (fourierCharacter k x) * ((r * a x i : ℝ) : ℂ) = _
    simp only [datumFourierIntegrand, Complex.ofReal_mul]
    ring
  simp only [datumFourierCoeff, hp, integral_const_mul, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul]

theorem datumFourierCoeff_finset_sum {I : Type*} (s : Finset I) (a : I → Field)
    (ha : ∀ j ∈ s, Continuous (a j)) :
    datumFourierCoeff (∑ j ∈ s, a j) = ∑ j ∈ s, datumFourierCoeff (a j) := by
  funext k i
  have hp (x : Vec) : datumFourierIntegrand (∑ j ∈ s, a j) k i x =
      ∑ j ∈ s, datumFourierIntegrand (a j) k i x := by
    have hv : ((∑ j ∈ s, a j) x) i = ∑ j ∈ s, a j x i := by
      simp only [Finset.sum_apply]
      exact map_sum (EuclideanSpace.proj i : Vec →L[ℝ] ℝ) (fun j => a j x) s
    unfold datumFourierIntegrand
    rw [hv]
    simp only [Complex.ofReal_sum, Finset.mul_sum]
  simp only [datumFourierCoeff, hp, Finset.sum_apply]
  exact integral_finsetSum s (fun j hj => datumFourierIntegrand_integrableOn (ha j hj) k i)

theorem datumFourierCoeff_laplacian (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    datumFourierCoeff (laplacian a) = laplacianCoefficient (datumFourierCoeff a) := by
  have hd (j : Fin 3) : ContDiff ℝ ∞ (coordinateDerivative a j) := tensorDir_contDiff ha j
  have hdp (j : Fin 3) : SpatialPeriodic (coordinateDerivative a j) :=
    tensorDir_periodic (ha.differentiable (by simp)) hp j
  have heq : laplacian a = ∑ j : Fin 3, coordinateDerivative (coordinateDerivative a j) j := by
    funext x
    simp only [laplacian, coordinateDerivative, Finset.sum_apply]
  rw [heq, datumFourierCoeff_finset_sum Finset.univ _ (fun j hj =>
    (tensorDir_contDiff (hd j) j).continuous)]
  simp_rw [SingularClosure.datumFourierCoeff_coordinateDerivative _ _ (hd _) (hdp _),
    SingularClosure.datumFourierCoeff_coordinateDerivative _ _ ha hp]
  exact sum_double_derivativeMultiplier (datumFourierCoeff a)

theorem datumFourierCoeff_laplacian_apply (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (k : Frequency) (i : Fin 3) :
    datumFourierCoeff (laplacian a) k i =
      -(laplaceSymbol k : ℂ) * datumFourierCoeff a k i := by
  rw [datumFourierCoeff_laplacian a ha hp]
  rfl

def scalarDatumFourierCoeff (p : Vec → ℝ) (k : Frequency) : ℂ :=
  ∫ x in unitCube, star (fourierCharacter k x) * (p x : ℂ)

theorem datumFourierCoeff_gradient (p : Vec → ℝ)
    (hp : ContDiff ℝ ∞ p) (hper : SpatialPeriodic p) (k : Frequency) (i : Fin 3) :
    datumFourierCoeff (gradient p) k i = derivativeSymbol i k * scalarDatumFourierCoeff p k := by
  let a : Field := fun x => WithLp.toLp 2 (fun _ : Fin 3 => p x)
  have ha : ContDiff ℝ ∞ a := (contDiff_piLp 2).2 (fun _ => hp)
  have hap : SpatialPeriodic a := by
    intro x j
    ext l
    exact hper x j
  have hderiv (x : Vec) : coordinateDerivative a i x i = fderiv ℝ p x (unitVector i) := by
    have hd := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x
      ((ha.differentiable (by simp)) x).hasFDerivAt
    have heq : (fun y => a y i) = p := rfl
    have he := congrArg (fun A : Vec →L[ℝ] ℝ => A (unitVector i)) hd.fderiv
    simpa only [Function.comp_def, EuclideanSpace.coe_proj, heq,
      ContinuousLinearMap.comp_apply, coordinateDerivative] using he.symm
  have h := congrFun (congrFun
    (SingularClosure.datumFourierCoeff_coordinateDerivative i a ha hap) k) i
  change (∫ x in unitCube, star (fourierCharacter k x) *
      (coordinateDerivative a i x i : ℂ)) = derivativeSymbol i k *
        (∫ x in unitCube, star (fourierCharacter k x) * (p x : ℂ)) at h
  simp_rw [hderiv] at h
  exact h

theorem coefficientLeray_frequency_mul (k : Frequency) (z : ℂ) :
    coefficientLeray k (fun i => (k i : ℂ) * z) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [coefficientLeray]
  · have hd := frequencySquare_ne_zero k hk
    have hsum : (∑ j : Fin 3, (k j : ℂ) * ((k j : ℂ) * z)) =
        (∑ j : Fin 3, (k j : ℂ) ^ 2) * z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    funext i
    simp only [coefficientLeray, if_neg hk, hsum, Pi.zero_apply]
    field_simp [hd] <;> ring

theorem coefficientLeray_datumFourierCoeff_gradient (p : Vec → ℝ)
    (hp : ContDiff ℝ ∞ p) (hper : SpatialPeriodic p) (k : Frequency) :
    coefficientLeray k (datumFourierCoeff (gradient p) k) = 0 := by
  have heq : datumFourierCoeff (gradient p) k =
      fun i => (k i : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I * scalarDatumFourierCoeff p k) := by
    funext i
    rw [datumFourierCoeff_gradient p hp hper]
    unfold derivativeSymbol
    push_cast
    ring
  rw [heq]
  exact coefficientLeray_frequency_mul k _

end
end QuantumAdapter.Obligations
