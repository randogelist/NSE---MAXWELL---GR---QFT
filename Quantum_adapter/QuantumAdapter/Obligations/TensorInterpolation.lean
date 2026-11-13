import QuantumAdapter.Assembly.Fourier
import QuantumAdapter.Obligations.TensorContraction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Periodic tensor interpolation from actual derivatives and cube integration by parts. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff NNReal ENNReal

namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual coordinate derivative, with arbitrary real inner-product codomain. -/
def tensorDir (f : Vec → E) (j : Fin 3) : Vec → E :=
  fun x => fderiv ℝ f x (unitVector j)

def tensorGradSq (f : Vec → E) (x : Vec) : ℝ :=
  ∑ j : Fin 3, ‖tensorDir f j x‖ ^ 2

/-- The first displayed index is the outer derivative. -/
def tensorHessSq (f : Vec → E) (x : Vec) : ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3, ‖tensorDir (tensorDir f l) j x‖ ^ 2

theorem tensorGradSq_nonneg (f : Vec → E) (x : Vec) : 0 ≤ tensorGradSq f x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem tensorHessSq_nonneg (f : Vec → E) (x : Vec) : 0 ≤ tensorHessSq f x :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem tensorDir_contDiff {f : Vec → E} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (tensorDir f j) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem tensorGradSq_contDiff {f : Vec → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (tensorGradSq f) := by
  apply ContDiff.sum
  intro j hj
  exact (tensorDir_contDiff hf j).norm_sq ℝ

theorem tensorHessSq_contDiff {f : Vec → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (tensorHessSq f) := by
  apply ContDiff.sum
  intro j hj
  apply ContDiff.sum
  intro l hl
  exact (tensorDir_contDiff (tensorDir_contDiff hf l) j).norm_sq ℝ

theorem tensorDir_periodic {f : Vec → E} (hf : Differentiable ℝ f)
    (hp : SpatialPeriodic f) (j : Fin 3) : SpatialPeriodic (tensorDir f j) := by
  intro x l
  have heq : (fun y : Vec => f (y + unitVector l)) = f := funext (fun y => hp y l)
  have hd := (hf (x + unitVector l)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const (unitVector l))
  have hd' : HasFDerivAt f (fderiv ℝ f (x + unitVector l)) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, heq] using hd
  exact congrArg (fun A : Vec →L[ℝ] E => A (unitVector j)) hd'.fderiv.symm

theorem tensorGradSq_periodic {f : Vec → E} (hf : Differentiable ℝ f)
    (hp : SpatialPeriodic f) : SpatialPeriodic (tensorGradSq f) := by
  intro x l
  unfold tensorGradSq
  apply Finset.sum_congr rfl
  intro j hj
  rw [tensorDir_periodic hf hp j x l]

theorem tensorDir_inner {f g : Vec → E} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (j : Fin 3) (x : Vec) :
    tensorDir (fun y => inner ℝ (f y) (g y)) j x =
      inner ℝ (f x) (tensorDir g j x) + inner ℝ (tensorDir f j x) (g x) :=
  fderiv_inner_apply ℝ (hf x) (hg x) (unitVector j)

theorem tensorDir_mul {f g : Vec → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (j : Fin 3) (x : Vec) :
    tensorDir (fun y => f y * g y) j x =
      f x * tensorDir g j x + g x * tensorDir f j x := by
  unfold tensorDir
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem tensorDir_norm_sq {f : Vec → E} (hf : Differentiable ℝ f)
    (j : Fin 3) (x : Vec) :
    tensorDir (fun y => ‖f y‖ ^ 2) j x = 2 * inner ℝ (f x) (tensorDir f j x) := by
  unfold tensorDir
  rw [(hf x).hasFDerivAt.norm_sq.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, two_smul, two_mul]

theorem tensorDir_gradSq {f : Vec → E} (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (x : Vec) :
    tensorDir (tensorGradSq f) j x =
      2 * ∑ l : Fin 3, inner ℝ (tensorDir f l x) (tensorDir (tensorDir f l) j x) := by
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun l hl =>
    (((tensorDir_contDiff hf l).differentiable (by simp)) x).hasFDerivAt.norm_sq)
  change fderiv ℝ (fun y => ∑ l : Fin 3, ‖tensorDir f l y‖ ^ 2) x (unitVector j) = _
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, two_smul, ← two_mul, ← Finset.mul_sum,
    tensorDir]

theorem integral_unitCube_tensorDir_real_eq_zero (f : Vec → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) :
    (∫ x in unitCube, tensorDir f j x) = 0 := by
  let g : Vec → ℂ := fun x => (f x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
  have hgp : SpatialPeriodic g := fun x l => congrArg Complex.ofReal (hp x l)
  have hzero := integral_unitCube_directionalDerivative_eq_zero g hg hgp j
  have hpoint (x : Vec) : fderiv ℝ g x (unitVector j) = ((tensorDir f j x : ℝ) : ℂ) := by
    rw [(Complex.ofRealCLM.hasFDerivAt.comp x
      ((hf.differentiable (by simp)) x).hasFDerivAt).fderiv]
    rfl
  have hi := (tensorDir_contDiff hf j).continuous.continuousOn.integrableOn_compact
    isCompact_unitCube (μ := volume)
  have hreal := congrArg Complex.re hzero
  simp_rw [hpoint] at hreal
  have hcomm : (∫ x in unitCube, ((tensorDir f j x : ℝ) : ℂ)) =
      (((∫ x in unitCube, tensorDir f j x) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hi
  rw [hcomm] at hreal
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_re, Complex.zero_re] using hreal

def tensorFlux (f : Vec → E) (j : Fin 3) (x : Vec) : ℝ :=
  inner ℝ (f x) (tensorDir f j x) * tensorGradSq f x

def tensorRemainder (f : Vec → E) (x : Vec) : ℝ :=
  (∑ j : Fin 3, inner ℝ (f x) (tensorDir (tensorDir f j) j x)) * tensorGradSq f x +
    2 * ∑ j : Fin 3, inner ℝ (f x) (tensorDir f j x) *
      (∑ l : Fin 3, inner ℝ (tensorDir f l x) (tensorDir (tensorDir f l) j x))

theorem tensorFlux_contDiff {f : Vec → E} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (tensorFlux f j) :=
  (hf.inner ℝ (tensorDir_contDiff hf j)).mul (tensorGradSq_contDiff hf)

theorem tensorRemainder_continuous {f : Vec → E} (hf : ContDiff ℝ ∞ f) :
    Continuous (tensorRemainder f) := by
  have hd (j : Fin 3) := (tensorDir_contDiff hf j).continuous
  have hdd (j l : Fin 3) := (tensorDir_contDiff (tensorDir_contDiff hf l) j).continuous
  unfold tensorRemainder
  exact ((continuous_finset_sum _ (fun j hj => hf.continuous.inner (hdd j j))).mul
    (tensorGradSq_contDiff hf).continuous).add
      (continuous_const.mul (continuous_finset_sum _ (fun j hj =>
        (hf.continuous.inner (hd j)).mul
          (continuous_finset_sum _ (fun l hl => (hd l).inner (hdd j l))))))

theorem tensorFlux_periodic {f : Vec → E} (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) (j : Fin 3) : SpatialPeriodic (tensorFlux f j) := by
  intro x l
  simp only [tensorFlux, hp x l,
    tensorDir_periodic (hf.differentiable (by simp)) hp j x l,
    tensorGradSq_periodic (hf.differentiable (by simp)) hp x l]

theorem tensorFlux_divergence {f : Vec → E} (hf : ContDiff ℝ ∞ f) (x : Vec) :
    (∑ j : Fin 3, tensorDir (tensorFlux f j) j x) =
      tensorGradSq f x ^ 2 + tensorRemainder f x := by
  have hpoint (j : Fin 3) : tensorDir (tensorFlux f j) j x =
      inner ℝ (f x) (tensorDir f j x) *
        (2 * ∑ l : Fin 3, inner ℝ (tensorDir f l x) (tensorDir (tensorDir f l) j x)) +
      tensorGradSq f x *
        (inner ℝ (f x) (tensorDir (tensorDir f j) j x) + ‖tensorDir f j x‖ ^ 2) := by
    change tensorDir (fun y => inner ℝ (f y) (tensorDir f j y) * tensorGradSq f y) j x = _
    rw [tensorDir_mul
      ((hf.inner ℝ (tensorDir_contDiff hf j)).differentiable (by simp))
      ((tensorGradSq_contDiff hf).differentiable (by simp)), tensorDir_gradSq hf,
      tensorDir_inner (hf.differentiable (by simp))
        ((tensorDir_contDiff hf j).differentiable (by simp)), real_inner_self_eq_norm_sq]
  have hpoint' (j : Fin 3) : tensorDir (tensorFlux f j) j x =
      ‖tensorDir f j x‖ ^ 2 * tensorGradSq f x +
      inner ℝ (f x) (tensorDir (tensorDir f j) j x) * tensorGradSq f x +
      2 * (inner ℝ (f x) (tensorDir f j x) *
        (∑ l : Fin 3, inner ℝ (tensorDir f l x) (tensorDir (tensorDir f l) j x))) := by
    rw [hpoint]
    ring
  simp_rw [hpoint']
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  unfold tensorRemainder tensorGradSq
  ring

theorem tensor_interpolation_integral_identity {f : Vec → E} (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) :
    (∫ x in unitCube, tensorGradSq f x ^ 2) =
      -(∫ x in unitCube, tensorRemainder f x) := by
  have hz (j : Fin 3) := integral_unitCube_tensorDir_real_eq_zero
    (tensorFlux f j) (tensorFlux_contDiff hf j) (tensorFlux_periodic hf hp j) j
  have hsum : (∫ x in unitCube, ∑ j : Fin 3, tensorDir (tensorFlux f j) j x) = 0 := by
    rw [integral_finsetSum Finset.univ (fun j hj =>
      (tensorDir_contDiff (tensorFlux_contDiff hf j) j).continuous.continuousOn.integrableOn_compact
        isCompact_unitCube)]
    simp only [hz, Finset.sum_const_zero]
  simp_rw [tensorFlux_divergence hf] at hsum
  have hGI : IntegrableOn (fun x => tensorGradSq f x ^ 2) unitCube volume :=
    ((tensorGradSq_contDiff hf).continuous.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hRI : IntegrableOn (tensorRemainder f) unitCube volume :=
    (tensorRemainder_continuous hf).continuousOn.integrableOn_compact isCompact_unitCube
  rw [integral_add (f := fun x => tensorGradSq f x ^ 2) (g := tensorRemainder f)
    (μ := volume.restrict unitCube) hGI hRI] at hsum
  linarith

/-- Continuous scalar functions on the cube have every finite integral norm. -/
theorem memLp_unitCube_of_continuous (u : Vec → ℝ) (hu : Continuous u) (p : ℝ≥0∞) :
    MemLp u p (volume.restrict unitCube) := by
  letI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using isCompact_unitCube.measure_lt_top⟩
  obtain ⟨C, hC⟩ := isCompact_unitCube.exists_bound_of_continuousOn
    (f := u) hu.continuousOn
  exact MemLp.of_bound hu.aestronglyMeasurable C
    ((ae_restrict_mem isCompact_unitCube.measurableSet).mono (fun x hx => hC x hx))

/-- Integral Cauchy--Schwarz in the exact square-root convention used here. -/
theorem integral_unitCube_mul_le_sqrt (u v : Vec → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) :
    (∫ x in unitCube, u x * v x) ≤
      Real.sqrt (∫ x in unitCube, u x ^ 2) * Real.sqrt (∫ x in unitCube, v x ^ 2) := by
  have hc : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict unitCube) hc
    (Filter.Eventually.of_forall hu0) (Filter.Eventually.of_forall hv0)
    (memLp_unitCube_of_continuous u hu (ENNReal.ofReal 2))
    (memLp_unitCube_of_continuous v hv (ENNReal.ofReal 2))
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

theorem tensorRemainder_bound {f : Vec → E} (x : Vec) :
    |tensorRemainder f x| ≤
      4 * ‖f x‖ * tensorGradSq f x * Real.sqrt (tensorHessSq f x) :=
  tensor_interpolation_integrand_bound (f x) (fun j => tensorDir f j x)
    (fun j l => tensorDir (tensorDir f l) j x)

/-- Tensor interpolation on the physical cube, with an explicit dimension-three
constant independent of the codomain dimension and of the Fourier cutoff. -/
theorem periodic_tensor_interpolation (f : Vec → E) (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) :
    Real.sqrt (∫ x in unitCube, tensorGradSq f x ^ 2) ≤
      4 * M * Real.sqrt (∫ x in unitCube, tensorHessSq f x) := by
  let A : ℝ := ∫ x in unitCube, tensorGradSq f x ^ 2
  let B : ℝ := ∫ x in unitCube, tensorHessSq f x
  have hA : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (tensorHessSq_nonneg f)
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hG := (tensorGradSq_contDiff hf).continuous
  have hH := (tensorHessSq_contDiff hf).continuous
  have hS : Continuous (fun x => Real.sqrt (tensorHessSq f x)) := hH.sqrt
  have hR : IntegrableOn (tensorRemainder f) unitCube volume :=
    (tensorRemainder_continuous hf).continuousOn.integrableOn_compact isCompact_unitCube
  have hI : IntegrableOn (fun x => tensorGradSq f x * Real.sqrt (tensorHessSq f x)) unitCube volume :=
    (hG.mul hS).continuousOn.integrableOn_compact isCompact_unitCube
  have hpoint (x : Vec) : -tensorRemainder f x ≤
      (4 * M) * (tensorGradSq f x * Real.sqrt (tensorHessSq f x)) := by
    calc
      _ ≤ |tensorRemainder f x| := neg_le_abs _
      _ ≤ 4 * ‖f x‖ * tensorGradSq f x * Real.sqrt (tensorHessSq f x) := tensorRemainder_bound x
      _ ≤ (4 * M) * (tensorGradSq f x * Real.sqrt (tensorHessSq f x)) := by
        have h := mul_le_mul_of_nonneg_right (hM x)
          (mul_nonneg (tensorGradSq_nonneg f x) (Real.sqrt_nonneg _))
        nlinarith
  have hfirst : A ≤ (4 * M) *
      (∫ x in unitCube, tensorGradSq f x * Real.sqrt (tensorHessSq f x)) := by
    have h := integral_mono hR.neg (hI.const_mul (4 * M)) hpoint
    rw [integral_neg, integral_const_mul, ← tensor_interpolation_integral_identity hf hp] at h
    exact h
  have hcs := integral_unitCube_mul_le_sqrt (tensorGradSq f)
    (fun x => Real.sqrt (tensorHessSq f x)) hG hS
    (tensorGradSq_nonneg f) (fun x => Real.sqrt_nonneg _)
  simp_rw [Real.sq_sqrt (tensorHessSq_nonneg f _)] at hcs
  have hlast : A ≤ 4 * M * (Real.sqrt A * Real.sqrt B) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
  have hsA := Real.sq_sqrt hA
  have hsA0 := Real.sqrt_nonneg A
  have hright : 0 ≤ 4 * M * Real.sqrt B := by positivity
  by_cases hz : Real.sqrt A = 0
  · simpa only [hz] using hright
  · have hsAp : 0 < Real.sqrt A := lt_of_le_of_ne hsA0 (Ne.symm hz)
    apply (mul_le_mul_left hsAp).mp
    nlinarith

end
end QuantumAdapter.Obligations
