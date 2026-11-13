import GRAssembly.ScalarJet
import GRAdapter.StressDivergence

/-! GC11: native scalar completion components and conservation identities. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology BigOperators ContDiff

namespace NSEGR.Assembly
noncomputable section

theorem nseSpatialSource3_trace
    (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hdiv : divergence (u t) x = 0) :
    trace3 (nseSpatialSource3 ν u p t x) =
      vectorSq3 (fun i => u t x i) + 3 * p t x := by
  have hz : trace3 (strain (u t) x) = 0 := by
    rw [trace3_eq_matrix_trace, trace_strain, hdiv, mul_zero]
  change strain (u t) x 0 0 + strain (u t) x 1 1 + strain (u t) x 2 2 = 0 at hz
  simp only [trace3, nseSpatialSource3, identity3_diag, mul_one, vectorSq3]
  linear_combination -ν * hz

theorem completedBoundary_lower_trace
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec)
    (hdiv : divergence (u t) x = 0) :
    lorentzTrace4 (lowerTensor4
      (conservedSourceUpper ν ρ u p t x + scalarCompletionUpper ψ t x)) =
      -ρ + vectorSq3 (fun i => u t x i) + 3 * p t x +
        3 * scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x -
        3 * scalarLaplacian (ψ t) x := by
  rw [lorentzTrace4_lowerTensor4, scalarCompletionUpper_eq_scalarJet]
  change lorentzTrace4 (scalarCompletedUpper ρ (fun i => u t x i)
    (nseSpatialSource3 ν u p t x) (scalarHessian (ψ t) x)
    (fun i => gradient (scalarLocalTimeDerivative ψ t) x i)
    (scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x)) = _
  rw [scalarCompletedUpper_eq_block, lorentzTrace4_boundaryBlock,
    trace3_scalarSpatialJet, nseSpatialSource3_trace ν u p t x hdiv,
    trace3_scalarHessian]
  ring

theorem completedBoundary_time_time
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec)
    (hdiv : divergence (u t) x = 0) :
    completedBoundary ν ρ u p ψ t x 0 0 =
      -(2 * ρ + vectorSq3 (fun i => u t x i)) / 3 - p t x -
        scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x := by
  simp only [completedBoundary, traceReverse4,
    completedBoundary_lower_trace ν ρ u p ψ t x hdiv,
    lowerTensor4_time_time, Matrix.add_apply, conservedSourceUpper_time_time,
    scalarCompletionUpper_time_time]
  norm_num [eta4, lorentzSign4]
  ring

theorem completedBoundary_time_space
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec) (i : Fin 3) :
    completedBoundary ν ρ u p ψ t x 0 i.succ =
      u t x i - gradient (scalarLocalTimeDerivative ψ t) x i := by
  simp [completedBoundary, traceReverse4, eta4, lorentzSign4,
    lowerTensor4, conservedSourceUpper, scalarCompletionUpper]

theorem completedBoundary_space_space
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec)
    (hdiv : divergence (u t) x = 0) (i j : Fin 3) :
    completedBoundary ν ρ u p ψ t x i.succ j.succ =
      ((vectorSq3 (fun l => u t x l) - ρ) / 3) * identity3 i j -
        u t x i * u t x j + ν * strain (u t) x i j - scalarHessian (ψ t) x i j := by
  simp only [completedBoundary, traceReverse4,
    completedBoundary_lower_trace ν ρ u p ψ t x hdiv,
    reconstruction_eta4_spatial, lowerTensor4_space_space, Matrix.add_apply,
    conservedSourceUpper_space_space, scalarCompletionUpper_space_space]
  ring

theorem completedBoundary_rawVelocity
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) :
    boundaryRawVelocity (completedBoundary ν ρ u p ψ) t =
      fun x => u t x - gradient (scalarLocalTimeDerivative ψ t) x := by
  funext x
  apply PiLp.ext
  intro i
  exact completedBoundary_time_space ν ρ u p ψ t x i

theorem completedBoundary_beta
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec)
    (hdiv : divergence (u t) x = 0) :
    boundaryBeta (completedBoundary ν ρ u p ψ) t x =
      ρ + scalarLaplacian (ψ t) x := by
  have hz : trace3 (strain (u t) x) = 0 := by
    rw [trace3_eq_matrix_trace, trace_strain, hdiv, mul_zero]
  have hH := trace3_scalarHessian (ψ t) x
  change strain (u t) x 0 0 + strain (u t) x 1 1 + strain (u t) x 2 2 = 0 at hz
  change scalarHessian (ψ t) x 0 0 + scalarHessian (ψ t) x 1 1 +
    scalarHessian (ψ t) x 2 2 = scalarLaplacian (ψ t) x at hH
  simp only [boundaryBeta, spatialIndex4,
    completedBoundary_space_space ν ρ u p ψ t x hdiv, identity3_diag,
    mul_one, Fin.sum_univ_succ]
  simp only [vectorSq3]
  linear_combination -ν * hz + hH

theorem nseSpatialSource3_divergence
    (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hu : ContDiff ℝ ∞ (u t)) (hp : DifferentiableAt ℝ (p t) x)
    (hdiv : ∀ y, divergence (u t) y = 0) :
    tensorDivergence (nseSpatialSource3 ν u p t) x =
      convection (u t) x + gradient (p t) x - ν • laplacian (u t) x := by
  have hu' := hu.differentiable (by simp)
  have ho : ∀ i j, DifferentiableAt ℝ (fun y => velocityOuter (u t y) i j) x :=
    fun i j => (velocityOuter_component_smooth hu i j).differentiable (by simp) x
  have hi : ∀ i j, DifferentiableAt ℝ (fun y => p t y * identity3 i j) x :=
    fun i j => hp.mul_const _
  have hs : ∀ i j, DifferentiableAt ℝ (fun y => strain (u t) y i j) x :=
    fun i j => (strain_component_smooth hu i j).differentiable (by simp) x
  have heq : nseSpatialSource3 ν u p t = fun y =>
      (velocityOuter (u t y) + (fun i j => p t y * identity3 i j)) -
        ν • strain (u t) y := by
    rfl
  rw [heq, tensorDivergence_sub _ _ x (fun i j => (ho i j).add (hi i j))
    (fun i j => (hs i j).const_smul ν), tensorDivergence_add _ _ x ho hi,
    tensorDivergence_velocityOuter_of_divergence_zero (hu' x) (hdiv x),
    tensorDivergence_isotropic _ _ hp, tensorDivergence_smul ν _ x hs,
    tensorDivergence_strain_of_divergence_zero hu (funext hdiv) x]

/-- The actual upper-index conservation operator in the fixed boundary coordinates. -/
def upperDivergence (T : BoundaryTensor) (t : ℝ) (x : Vec) (b : Fin 4) : ℝ :=
  ∑ a : Fin 4, boundaryPartial (fun s y => T s y a b) a t x

theorem velocity_coordinate_timeDerivative
    {u : Velocity} {t : ℝ} {x : Vec}
    (hu : AnalyticAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x)) (i : Fin 3) :
    deriv (fun s => u s x i) t = localTimeDerivative u t x i := by
  let ev : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
  have h := ev.hasFDerivAt.comp t hu.curry_left.differentiableAt.hasFDerivAt
  simpa only [localTimeDerivative, ContinuousLinearMap.comp_apply,
    Function.comp_def] using h.hasDerivAt.deriv

theorem nseSpatialSource3_symmetric
    (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec) (i j : Fin 3) :
    nseSpatialSource3 ν u p t x i j = nseSpatialSource3 ν u p t x j i := by
  have hid : identity3 i j = identity3 j i := by
    simp only [identity3, eq_comm]
  simp only [nseSpatialSource3, strain, hid]
  ring

theorem conservedSourceUpper_divergence_time
    (ν ρ : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hu : DifferentiableAt ℝ (u t) x) :
    upperDivergence (conservedSourceUpper ν ρ u p) t x 0 = divergence (u t) x := by
  simp only [upperDivergence, Fin.sum_univ_succ, boundaryPartial,
    conservedSourceUpper, boundaryBlock, Fin.cases_zero, Fin.cases_succ,
    deriv_const, zero_add]
  simp only [StressCalc.component_fderiv hu, divergence, spatialPartial,
    Fin.sum_univ_succ]

theorem conservedSourceUpper_divergence_space
    (ν ρ : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hu : ContDiff ℝ ∞ (u t))
    (hjoint : AnalyticAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x))
    (hp : DifferentiableAt ℝ (p t) x)
    (hdiv : ∀ y, divergence (u t) y = 0) (i : Fin 3) :
    upperDivergence (conservedSourceUpper ν ρ u p) t x i.succ =
      nseResidual ν u p t x i := by
  have heq : upperDivergence (conservedSourceUpper ν ρ u p) t x i.succ =
      deriv (fun s => u s x i) t + tensorDivergence (nseSpatialSource3 ν u p t) x i := by
    simp only [upperDivergence, Fin.sum_univ_succ, boundaryPartial,
      conservedSourceUpper, boundaryBlock, Fin.cases_zero, Fin.cases_succ]
    change deriv (fun s => u s x i) t +
      (fderiv ℝ (fun y => nseSpatialSource3 ν u p t y 0 i) x (unitVector 0) +
        (fderiv ℝ (fun y => nseSpatialSource3 ν u p t y 1 i) x (unitVector 1) +
          (fderiv ℝ (fun y => nseSpatialSource3 ν u p t y 2 i) x (unitVector 2) + 0))) = _
    simp only [nseSpatialSource3_symmetric ν u p t _ _ i]
    rfl
  rw [heq, velocity_coordinate_timeDerivative hjoint,
    nseSpatialSource3_divergence ν u p t x hu hp hdiv]
  simp only [nseResidual, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
  ring

theorem conservedSourceUpper_conserved
    (ν ρ : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hu : ContDiff ℝ ∞ (u t))
    (hjoint : AnalyticAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x))
    (hp : DifferentiableAt ℝ (p t) x)
    (hdiv : ∀ y, divergence (u t) y = 0)
    (hmomentum : nseResidual ν u p t x = 0) :
    ∀ b, upperDivergence (conservedSourceUpper ν ρ u p) t x b = 0 := by
  intro b
  refine Fin.cases ?_ (fun i => ?_) b
  · rw [conservedSourceUpper_divergence_time ν ρ u p t x
      (hu.differentiable (by simp) x), hdiv]
  · rw [conservedSourceUpper_divergence_space ν ρ u p t x hu hjoint hp hdiv,
      hmomentum]
    rfl

end
end NSEGR.Assembly
