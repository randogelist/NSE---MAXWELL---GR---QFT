import GRAssembly.GaussianConstraints
import GRAdapter.ScalarCompatibility
import GRAdapter.Locality

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2400000

namespace NSEGR.Assembly
open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

def matrixEntryCLM (n : ℕ) (a b : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M a b
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem matrixEntryCLM_apply (n : ℕ) (a b : Fin n)
    (M : Matrix (Fin n) (Fin n) ℝ) : matrixEntryCLM n a b M = M a b := rfl

theorem analyticAt_matrix_entry {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Matrix (Fin n) (Fin n) ℝ} {z : E}
    (hf : AnalyticAt ℝ f z) (a b : Fin n) :
    AnalyticAt ℝ (fun y => f y a b) z :=
  ((matrixEntryCLM n a b).analyticAt _).comp hf

theorem analyticAt_matrix_of_entries {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Matrix (Fin n) (Fin n) ℝ} {z : E}
    (hf : ∀ a b, AnalyticAt ℝ (fun y => f y a b) z) :
    AnalyticAt ℝ f z := by
  have hsingle (a b : Fin n) :
      AnalyticAt ℝ (fun y => Matrix.single a b (f y a b)) z := by
    let L : ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
      LinearMap.toContinuousLinearMap (Matrix.singleLinearMap ℝ a b)
    have hc := (L.analyticAt (f z a b)).comp (hf a b)
    change AnalyticAt ℝ (fun y => L (f y a b)) z
    exact hc
  have hsum : AnalyticAt ℝ
      (fun y => ∑ a : Fin n, ∑ b : Fin n, Matrix.single a b (f y a b)) z := by
    apply Finset.analyticAt_fun_sum
    intro a ha
    apply Finset.analyticAt_fun_sum
    intro b hb
    exact hsingle a b
  have he : (fun y => ∑ a : Fin n, ∑ b : Fin n,
      Matrix.single a b (f y a b)) = f := by
    funext y
    exact (Matrix.matrix_eq_sum_single (f y)).symm
  rw [he] at hsum
  exact hsum

theorem matrix_entry_fderiv {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Matrix (Fin n) (Fin n) ℝ} {z : E}
    (hf : DifferentiableAt ℝ f z) (v : E) (a b : Fin n) :
    fderiv ℝ (fun y => f y a b) z v = (fderiv ℝ f z v) a b := by
  have he := (matrixEntryCLM n a b).hasFDerivAt.comp z hf.hasFDerivAt
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv

def boundaryEmbed : (ℝ × Vec) →L[ℝ] Bulk :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => bulkPoint 0 z.1 z.2
      map_add' := by
        intro a b
        apply PiLp.ext
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
      map_smul' := by
        intro c a
        apply PiLp.ext
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl }

@[simp] theorem boundaryEmbed_apply (z : ℝ × Vec) :
    boundaryEmbed z = bulkPoint 0 z.1 z.2 := rfl

theorem boundaryEmbed_time : boundaryEmbed (1, 0) = bulkBasis 1 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [boundaryEmbed, bulkPoint, bulkBasis,
    EuclideanSpace.single, PiLp.single_apply] <;> rfl

theorem boundaryEmbed_space (i : Fin 3) :
    boundaryEmbed (0, unitVector i) = bulkBasis i.succ.succ := by
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryEmbed, bulkPoint, bulkBasis, unitVector,
      EuclideanSpace.single, PiLp.single_apply] <;> rfl

theorem analyticAt_bulkPartial {f : Bulk → ℝ} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (i : Fin 5) :
    AnalyticAt ℝ (bulkPartial f i) z := by
  exact ((ContinuousLinearMap.apply ℝ ℝ (bulkBasis i)).analyticAt _).comp hf.fderiv

theorem boundaryPartial_restrict {f : Bulk → ℝ} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ f (bulkPoint 0 t x)) (a : Fin 4) :
    boundaryPartial (fun s y => f (bulkPoint 0 s y)) a t x =
      bulkPartial f a.succ (bulkPoint 0 t x) := by
  have hemb : AnalyticAt ℝ (fun z : ℝ × Vec => bulkPoint 0 z.1 z.2) (t, x) := by
    simpa only [boundaryEmbed_apply] using (boundaryEmbed.analyticAt (t, x))
  have hr : AnalyticAt ℝ (fun z : ℝ × Vec => f (bulkPoint 0 z.1 z.2)) (t, x) :=
    hf.comp (f := fun z : ℝ × Vec => bulkPoint 0 z.1 z.2) (x := (t, x)) hemb
  have hd := hf.differentiableAt.hasFDerivAt.comp (t, x)
    (boundaryEmbed.hasFDerivAt)
  have hd' : fderiv ℝ (fun z : ℝ × Vec => f (bulkPoint 0 z.1 z.2)) (t, x) =
      (fderiv ℝ f (bulkPoint 0 t x)).comp boundaryEmbed := by
    simpa only [Function.comp_def, boundaryEmbed_apply] using hd.fderiv
  refine Fin.cases ?_ (fun i => ?_) a
  · change deriv (fun s => f (bulkPoint 0 s x)) t = _
    rw [scalar_timeDerivative_eq_joint hr]
    change fderiv ℝ (fun z : ℝ × Vec => f (bulkPoint 0 z.1 z.2)) (t, x) (1, 0) = _
    rw [hd']
    simpa only [ContinuousLinearMap.comp_apply, boundaryEmbed_time, bulkPartial]
  · change fderiv ℝ (fun y => f (bulkPoint 0 t y)) x (unitVector i) = _
    rw [scalar_spatialDerivative_eq_joint hr i]
    change fderiv ℝ (fun z : ℝ × Vec => f (bulkPoint 0 z.1 z.2)) (t, x)
      (0, unitVector i) = _
    rw [hd']
    simpa only [ContinuousLinearMap.comp_apply, boundaryEmbed_space, bulkPartial]

theorem boundaryPartial_congr {f q : Pressure} {t : ℝ} {x : Vec}
    (he : (fun z : ℝ × Vec => f z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z : ℝ × Vec => q z.1 z.2)) (a : Fin 4) :
    boundaryPartial f a t x = boundaryPartial q a t x := by
  refine Fin.cases ?_ (fun i => ?_) a
  · have hm : Tendsto (fun s : ℝ => (s, x)) (𝓝 t) (𝓝 (t, x)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (he.comp_tendsto hm).deriv_eq
  · have hm : Tendsto (fun y : Vec => (t, y)) (𝓝 x) (𝓝 (t, x)) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i))
      (he.comp_tendsto hm).fderiv_eq

theorem bulkPartial_tangent_zero {f : Bulk → ℝ} {t : ℝ} {x : Vec} {c : ℝ}
    (hf : AnalyticAt ℝ f (bulkPoint 0 t x))
    (he : (fun z : ℝ × Vec => f (bulkPoint 0 z.1 z.2)) =ᶠ[𝓝 (t, x)]
      (fun _ => c)) (a : Fin 4) :
    bulkPartial f a.succ (bulkPoint 0 t x) = 0 := by
  rw [← boundaryPartial_restrict hf]
  rw [boundaryPartial_congr (q := fun _ _ => c) he]
  fin_cases a <;> simp [boundaryPartial]

theorem bulkPartial_radial_restrict {f : Bulk → ℝ} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ f (bulkPoint 0 t x)) :
    deriv (fun r : ℝ => f (bulkPoint r t x)) 0 =
      bulkPartial f 0 (bulkPoint 0 t x) := by
  have he : (fun r : ℝ => bulkPoint r t x) =
      (fun r => r • bulkBasis 0 + bulkPoint 0 t x) := by
    funext r
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [bulkPoint, bulkBasis, EuclideanSpace.single,
      PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply] <;> rfl
  have hd : HasDerivAt (fun r : ℝ => bulkPoint r t x) (bulkBasis 0) 0 := by
    rw [he]
    simpa only [one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (bulkBasis 0)).add_const (bulkPoint 0 t x))
  exact (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hd).deriv

theorem analyticAt_matrix_inverse {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det) :
    AnalyticAt ℝ (fun y => (h y)⁻¹) z := by
  have hu : IsUnit (h z) := (h z).isUnit_iff_isUnit_det.mpr hn
  have hi : AnalyticAt ℝ (fun H : Tensor4 => H⁻¹) (h z) := by
    have he : (fun H : Tensor4 => H⁻¹) = Ring.inverse := by
      funext H
      exact Matrix.nonsing_inv_eq_ringInverse H
    rw [he]
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) hu.unit)
  exact hi.comp hh

theorem bulkPartial_inverse {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det)
    (i : Fin 5) (a b : Fin 4) :
    bulkPartial (fun y => (h y)⁻¹ a b) i z =
      -∑ c : Fin 4, ∑ d : Fin 4,
        (h z)⁻¹ a c * bulkPartial (fun y => h y c d) i z * (h z)⁻¹ d b := by
  have hu : IsUnit (h z) := (h z).isUnit_iff_isUnit_det.mpr hn
  have hi0 : HasFDerivAt (fun H : Tensor4 => H⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Tensor4 (h z)⁻¹ (h z)⁻¹) (h z) := by
    have he : (fun H : Tensor4 => H⁻¹) = Ring.inverse := by
      funext H
      exact Matrix.nonsing_inv_eq_ringInverse H
    rw [he]
    simpa only [Matrix.coe_units_inv, IsUnit.unit_spec]
      using (hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit)
  have hi := hi0.comp z hh.differentiableAt.hasFDerivAt
  have hi' : HasFDerivAt (fun y => (h y)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ Tensor4 (h z)⁻¹ (h z)⁻¹).comp
        (fderiv ℝ h z)) z := by
    exact hi
  have hv := congrArg (fun L : Bulk →L[ℝ] Tensor4 =>
    matrixEntryCLM 4 a b (L (bulkBasis i))) hi'.fderiv
  have hc : bulkPartial (fun y => (h y)⁻¹ a b) i z =
      -((h z)⁻¹ * (fderiv ℝ h z (bulkBasis i)) * (h z)⁻¹) a b := by
    calc
      _ = matrixEntryCLM 4 a b (fderiv ℝ (fun y => (h y)⁻¹) z (bulkBasis i)) :=
        matrix_entry_fderiv (analyticAt_matrix_inverse hh hn).differentiableAt _ a b
      _ = _ := by
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.mulLeftRight_apply, matrixEntryCLM_apply,
          Matrix.neg_apply] using hv
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.neg_apply,
    Matrix.mul_apply, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  exact congrArg (fun q : ℝ => (h z)⁻¹ a c * q * (h z)⁻¹ d b)
    (matrix_entry_fderiv hh.differentiableAt (bulkBasis i) c d).symm

theorem analyticAt_gaussianSecondForm {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) : AnalyticAt ℝ (gaussianSecondForm h) z := by
  apply analyticAt_matrix_of_entries
  intro a b
  exact analyticAt_const.mul
    (analyticAt_bulkPartial (analyticAt_matrix_entry hh a b) 0)

theorem analyticAt_gaussianShape {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det) :
    AnalyticAt ℝ (gaussianShapeOperator h) z := by
  apply analyticAt_matrix_of_entries
  intro a b
  apply Finset.analyticAt_fun_sum
  intro c hc
  exact (analyticAt_matrix_entry (analyticAt_matrix_inverse hh hn) a c).mul
    (analyticAt_matrix_entry (analyticAt_gaussianSecondForm hh) c b)

theorem analyticAt_gaussianTangentialChristoffel {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det) (a b c : Fin 4) :
    AnalyticAt ℝ (fun y => gaussianTangentialChristoffel h y a b c) z := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact (analyticAt_matrix_entry (analyticAt_matrix_inverse hh hn) a d).mul
    (((analyticAt_bulkPartial (analyticAt_matrix_entry hh d c) b.succ).add
      (analyticAt_bulkPartial (analyticAt_matrix_entry hh d b) c.succ)).sub
        (analyticAt_bulkPartial (analyticAt_matrix_entry hh b c) d.succ))

@[simp] theorem eta4_inverse : eta4Matrix⁻¹ = eta4Matrix := by
  apply Matrix.inv_eq_right_inv
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, eta4Matrix, eta4, lorentzSign4,
      Matrix.one_apply]

theorem gaussianShape_at_flat {h : Bulk → Tensor4} {z : Bulk}
    (he : h z = eta4Matrix) (a b : Fin 4) :
    gaussianShapeOperator h z a b = lorentzSign4 a * gaussianSecondForm h z a b := by
  simp only [gaussianShapeOperator, he, eta4_inverse]
  fin_cases a <;> fin_cases b <;>
    norm_num [eta4Matrix, eta4, lorentzSign4, Fin.sum_univ_succ]

theorem bulkPartial_inverse_at_flat {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det) (he : h z = eta4Matrix)
    (a b : Fin 4) :
    bulkPartial (fun y => (h y)⁻¹ a b) 0 z =
      -2 * lorentzSign4 a * lorentzSign4 b * gaussianSecondForm h z a b := by
  rw [bulkPartial_inverse hh hn, he, eta4_inverse]
  fin_cases a <;> fin_cases b <;>
    norm_num [eta4Matrix, eta4, lorentzSign4, Fin.sum_univ_succ, gaussianSecondForm] <;> ring

end
end NSEGR.Assembly
