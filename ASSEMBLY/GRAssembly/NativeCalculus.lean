import GRAssembly.ScalarCompletion
import GRAssembly.HodgeLocal

/-! Ordinary tangential derivatives and analytic coordinate calculus. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

def tensor4Entry (a b : Fin 4) : Tensor4 →L[ℝ] ℝ :=
  ({ toFun := fun M => M a b
     map_add' := by intro M N; rfl
     map_smul' := by intro c M; rfl } : Tensor4 →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem analyticAt_tensor4_entry {f : ℝ × Vec → Tensor4} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (a b : Fin 4) :
    AnalyticAt ℝ (fun y => f y a b) z :=
  ((tensor4Entry a b).analyticAt _).comp hf

theorem analyticAt_tensor4_of_entries {f : ℝ × Vec → Tensor4} {z : ℝ × Vec}
    (hf : ∀ a b, AnalyticAt ℝ (fun y => f y a b) z) : AnalyticAt ℝ f z := by
  have h : AnalyticAt ℝ (fun y => ∑ a : Fin 4, ∑ b : Fin 4,
      f y a b • (Matrix.stdBasisMatrix a b (1 : ℝ))) z :=
    AnalyticAt.sum (fun a _ => AnalyticAt.sum (fun b _ =>
      (hf a b).smul analyticAt_const))
  convert h using 1
  funext y
  ext i j
  simp [Matrix.stdBasisMatrix]

theorem analyticAt_vec_of_components {f : ℝ × Vec → Vec} {z : ℝ × Vec}
    (hf : ∀ i, AnalyticAt ℝ (fun y => f y i) z) : AnalyticAt ℝ f z := by
  have h := AnalyticAt.pi hf
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.analyticAt _).comp h

theorem analyticOnNhd_slab_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ × Vec → E} {I : Set ℝ}
    (hf : AnalyticOnNhd ℝ f {z : ℝ × Vec | z.1 ∈ I}) :
    ContDiffOn ℝ ∞ f {z : ℝ × Vec | z.1 ∈ I} := by
  intro z hz
  exact (hf z hz).contDiffAt.contDiffWithinAt

theorem analyticOnNhd_slab_slice_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ × Vec → E} {I : Set ℝ}
    (hf : AnalyticOnNhd ℝ f {z : ℝ × Vec | z.1 ∈ I})
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (fun x => f (t, x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact ((hf (t, x) ht).comp (analyticAt_const.prodMk analyticAt_id)).contDiffAt

theorem jointSpace_jointSpace {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (i j : Fin 3) :
    jointSpace (jointSpace f i) j z = jointSpace (jointSpace f j) i z := by
  have hi : jointSpace f i =ᶠ[𝓝 z] scalarJointPartial f (0, unitVector i) := by
    filter_upwards [hf.eventually_analyticAt] with y hy
    exact scalar_spatialDerivative_eq_joint hy i
  have hj : jointSpace f j =ᶠ[𝓝 z] scalarJointPartial f (0, unitVector j) := by
    filter_upwards [hf.eventually_analyticAt] with y hy
    exact scalar_spatialDerivative_eq_joint hy j
  calc
    _ = jointSpace (scalarJointPartial f (0, unitVector i)) j z := jointSpace_congr hi j
    _ = scalarJointPartial (scalarJointPartial f (0, unitVector i))
        (0, unitVector j) z :=
      scalar_spatialDerivative_eq_joint (analyticAt_scalarJointPartial hf _) j
    _ = scalarJointPartial (scalarJointPartial f (0, unitVector j))
        (0, unitVector i) z := scalarJointPartial_commute hf _ _
    _ = jointSpace (scalarJointPartial f (0, unitVector j)) i z :=
      (scalar_spatialDerivative_eq_joint (analyticAt_scalarJointPartial hf _) i).symm
    _ = _ := jointSpace_congr hj.symm i

theorem jointTime_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × Vec → ℝ}
    {z : ℝ × Vec} (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) z) :
    jointTime (fun y => ∑ i ∈ s, f i y) z = ∑ i ∈ s, jointTime (f i) z := by
  exact (HasDerivAt.sum (fun i hi => (hf i hi).curry_left.differentiableAt.hasDerivAt)).deriv

theorem jointSpace_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × Vec → ℝ}
    {z : ℝ × Vec} (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) z) (j : Fin 3) :
    jointSpace (fun y => ∑ i ∈ s, f i y) j z = ∑ i ∈ s, jointSpace (f i) j z := by
  have h := HasFDerivAt.sum (fun i hi =>
    ((hf i hi).comp (analyticAt_const.prodMk analyticAt_id)).differentiableAt.hasFDerivAt)
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) h.fderiv

theorem jointTime_add {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) :
    jointTime (fun y => f y + g y) z = jointTime f z + jointTime g z :=
  deriv_fun_add hf.curry_left.differentiableAt hg.curry_left.differentiableAt

theorem jointSpace_add {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) (j : Fin 3) :
    jointSpace (fun y => f y + g y) j z = jointSpace f j z + jointSpace g j z := by
  have h := (((hf.comp (analyticAt_const.prodMk analyticAt_id)).differentiableAt.hasFDerivAt).add
    ((hg.comp (analyticAt_const.prodMk analyticAt_id)).differentiableAt.hasFDerivAt)).fderiv
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) h

theorem jointSpace_sub {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) (j : Fin 3) :
    jointSpace (fun y => f y - g y) j z = jointSpace f j z - jointSpace g j z := by
  have h := (((hf.comp (analyticAt_const.prodMk analyticAt_id)).differentiableAt.hasFDerivAt).sub
    ((hg.comp (analyticAt_const.prodMk analyticAt_id)).differentiableAt.hasFDerivAt)).fderiv
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) h

@[simp] theorem jointTime_neg (f : ℝ × Vec → ℝ) (z : ℝ × Vec) :
    jointTime (fun y => -f y) z = -jointTime f z := by simp [jointTime]

@[simp] theorem jointSpace_neg (f : ℝ × Vec → ℝ) (j : Fin 3) (z : ℝ × Vec) :
    jointSpace (fun y => -f y) j z = -jointSpace f j z := by simp [jointSpace]

theorem analyticAt_gradient_joint {ψ : Pressure} {z : ℝ × Vec}
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => gradient (ψ y.1) y.2) z := by
  apply analyticAt_vec_of_components
  intro i
  exact analyticAt_jointSpace hψ i

theorem analyticAt_boundaryBeta {K : BoundaryTensor} {z : ℝ × Vec}
    (hK : AnalyticAt ℝ (fun y : ℝ × Vec => K y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => boundaryBeta K y.1 y.2) z := by
  exact (AnalyticAt.sum (fun i _ => analyticAt_tensor4_entry hK i.succ i.succ)).neg

theorem analyticAt_boundaryRawVelocity {K : BoundaryTensor} {z : ℝ × Vec}
    (hK : AnalyticAt ℝ (fun y : ℝ × Vec => K y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => boundaryRawVelocity K y.1 y.2) z := by
  apply analyticAt_vec_of_components
  intro i
  exact analyticAt_tensor4_entry hK 0 i.succ

theorem scalar_time_laplacian_commute {ψ : Pressure} {t : ℝ} {x : Vec}
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) (t, x)) :
    scalarLocalTimeDerivative (fun s => scalarLaplacian (ψ s)) t x =
      scalarLaplacian (scalarLocalTimeDerivative ψ t) x := by
  let f : ℝ × Vec → ℝ := fun z => ψ z.1 z.2
  change jointTime (fun z => ∑ i : Fin 3, jointSpace (jointSpace f i) i z) (t, x) =
    ∑ i : Fin 3, jointSpace (jointSpace (jointTime f) i) i (t, x)
  rw [jointTime_sum _ (fun i _ => analyticAt_jointSpace (analyticAt_jointSpace hψ i) i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jointTime_jointSpace (analyticAt_jointSpace hψ i) i]
  apply jointSpace_congr
  filter_upwards [hψ.eventually_analyticAt] with z hz
  exact jointTime_jointSpace hz i

theorem scalar_time_gradient_commute {ψ : Pressure} {t : ℝ} {x : Vec}
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) (t, x)) :
    localTimeDerivative (fun s => gradient (ψ s)) t x =
      gradient (scalarLocalTimeDerivative ψ t) x := by
  apply PiLp.ext
  intro i
  rw [← velocity_coordinate_timeDerivative (analyticAt_gradient_joint hψ) i]
  exact jointTime_jointSpace hψ i

end
end NSEGR.Assembly
