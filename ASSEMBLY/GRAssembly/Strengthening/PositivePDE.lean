import GRAssembly.Strengthening.Calculus
import NSEMaxwell.Spacetime

/-!
Actual local pressure uniqueness and extension of the forward NSE residual
through the initial hypersurface. Every derivative is the native derivative;
no pressure-recovery, smoothing or endpoint-regularity contract is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped ContDiff Topology BigOperators

namespace NSEGR.Strengthening
noncomputable section

theorem localNSE_originNormalize {ν τ δ : ℝ} {u : Velocity} {p : Pressure}
    (h : LocalNSE ν τ δ u p) : LocalNSE ν τ δ u (originNormalize p) := by
  refine {
    radius_pos := h.radius_pos
    velocity_analytic := h.velocity_analytic
    pressure_analytic := ?_
    periodic_velocity := h.periodic_velocity
    periodic_pressure := ?_
    divergence_free := h.divergence_free
    momentum := ?_ }
  · intro z hz
    have hmap : AnalyticAt ℝ (fun w : ℝ × Vec => (w.1, (0 : Vec))) z :=
      analyticAt_fst.prod analyticAt_const
    have hp0 : AnalyticAt ℝ (fun w : ℝ × Vec => p w.1 0) z :=
      (h.pressure_analytic (z.1, 0) hz).comp_of_eq hmap rfl
    exact (h.pressure_analytic z hz).sub hp0
  · intro t ht x i
    change p t (x + unitVector i) - p t 0 = p t x - p t 0
    rw [h.periodic_pressure t ht x i]
  · intro t ht x
    have hg : gradient (originNormalize p t) = gradient (p t) :=
      originNormalize_gradient p t
    simpa only [nseResidual, hg] using h.momentum t ht x

theorem fderiv_eq_of_gradient_eq {p q : ScalarField}
    (hgrad : gradient p = gradient q) (x : Vec) :
    fderiv ℝ p x = fderiv ℝ q x := by
  have hc (i : Fin 3) :
      fderiv ℝ p x (unitVector i) = fderiv ℝ q x (unitVector i) := by
    simpa only [gradient, PiLp.toLp_apply] using
      congrArg (fun w : Vec => w i) (congrFun hgrad x)
  apply ContinuousLinearMap.ext
  intro v
  have hv : (∑ i : Fin 3, v i • unitVector i) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      unitVector] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  rw [← hv]
  simp only [map_sum, map_smul, hc]

theorem originNormalize_eq_of_gradient_eq {p q : ScalarField}
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q)
    (hgrad : gradient p = gradient q) :
    (fun x : Vec => p x - p 0) = (fun x : Vec => q x - q 0) := by
  apply eq_of_fderiv_eq (hp.sub_const (p 0)) (hq.sub_const (q 0))
    (fun x => ?_) (0 : Vec) (by simp)
  simpa only [fderiv_sub_const] using fderiv_eq_of_gradient_eq hgrad x

theorem localNSE_gradient_eq_of_eventuallyEq
    {ν τ σ δ ε t : ℝ} {u v : Velocity} {p q : Pressure}
    (hn : LocalNSE ν τ δ u p) (hm : LocalNSE ν σ ε v q)
    (htu : t ∈ timeInterval τ δ) (htv : t ∈ timeInterval σ ε)
    (hV : u =ᶠ[𝓝 t] v) : gradient (p t) = gradient (q t) := by
  have hs : u t = v t := hV.eq_of_nhds
  funext x
  have hevent : (fun s : ℝ => u s x) =ᶠ[𝓝 t] (fun s : ℝ => v s x) :=
    hV.mono (fun s hs' => congrFun hs' x)
  have hdt : localTimeDerivative u t x = localTimeDerivative v t x := hevent.deriv_eq
  have hp := hn.momentum t htu x
  have hq := hm.momentum t htv x
  unfold nseResidual at hp hq
  rw [hdt, hs] at hp
  exact add_left_cancel ((sub_eq_zero.mp hp).trans (sub_eq_zero.mp hq).symm)

theorem localNSE_originNormalize_eq_of_eventuallyEq
    {ν τ σ δ ε t : ℝ} {u v : Velocity} {p q : Pressure}
    (hn : LocalNSE ν τ δ u p) (hm : LocalNSE ν σ ε v q)
    (htu : t ∈ timeInterval τ δ) (htv : t ∈ timeInterval σ ε)
    (hV : u =ᶠ[𝓝 t] v) : originNormalize p t = originNormalize q t := by
  have hp : Differentiable ℝ (p t) := by
    intro x
    exact ((hn.pressure_analytic (t, x) htu).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hq : Differentiable ℝ (q t) := by
    intro x
    exact ((hm.pressure_analytic (t, x) htv).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  exact originNormalize_eq_of_gradient_eq hp hq
    (localNSE_gradient_eq_of_eventuallyEq hn hm htu htv hV)

theorem closure_positiveSpacetime :
    closure positiveSpacetime = NSEMaxwell.Classical.forwardSpacetime := by
  have hprod : positiveSpacetime = Ioi (0 : ℝ) ×ˢ (univ : Set Vec) := by
    ext z
    simp [positiveSpacetime]
  rw [hprod, NSEMaxwell.Spacetime.forwardSpacetime_eq_prod, closure_prod_eq]
  simp

theorem continuousOn_forward_eq_zero_of_positive
    {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    {f : ℝ × Vec → E}
    (hf : ContinuousOn f NSEMaxwell.Classical.forwardSpacetime)
    (hz : ∀ z ∈ positiveSpacetime, f z = 0) :
    ∀ z ∈ NSEMaxwell.Classical.forwardSpacetime, f z = 0 := by
  have he : EqOn f (fun _ => 0) positiveSpacetime := hz
  refine he.of_subset_closure hf continuousOn_const ?_ ?_
  · intro z hz'
    change 0 < z.1 at hz'
    change 0 ≤ z.1
    exact hz'.le
  · rw [closure_positiveSpacetime]

theorem forward_gradient_smooth {p : Pressure}
    (hp : NSEMaxwell.Classical.SmoothPressure p) :
    NSEMaxwell.Classical.SmoothVelocity
      (fun t => NSEMaxwell.Classical.gradient (p t)) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  apply (NSEMaxwell.Spacetime.directional_smooth hp
    (0, NSEMaxwell.Classical.unitVector i)).congr
  intro z hz
  simpa only [NSEMaxwell.Classical.gradient, PiLp.toLp_apply] using
    NSEMaxwell.Spacetime.spatial_restriction_fderiv hp hz z.2
      (NSEMaxwell.Classical.unitVector i)

theorem forward_convection_smooth {u : Velocity}
    (hu : NSEMaxwell.Classical.SmoothVelocity u) :
    NSEMaxwell.Classical.SmoothVelocity
      (fun t => NSEMaxwell.Classical.convection (u t)) := by
  have hd : ContDiffOn ℝ ∞
      (fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        NSEMaxwell.Classical.forwardSpacetime)
      NSEMaxwell.Classical.forwardSpacetime :=
    hu.fderivWithin (m := ∞) NSEMaxwell.Spacetime.uniqueDiffOn_forwardSpacetime
      (by simp)
  have hv : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => ((0 : ℝ), u z.1 z.2))
      NSEMaxwell.Classical.forwardSpacetime := contDiffOn_const.prodMk hu
  apply (hd.clm_apply hv).congr
  intro z hz
  exact NSEMaxwell.Spacetime.spatial_restriction_fderiv hu hz z.2 (u z.1 z.2)

theorem forward_laplacian_smooth {u : Velocity}
    (hu : NSEMaxwell.Classical.SmoothVelocity u) :
    NSEMaxwell.Classical.SmoothVelocity
      (fun t => NSEMaxwell.Classical.laplacian (u t)) := by
  change ContDiffOn ℝ ∞
    (fun z : ℝ × Vec => ∑ i : Fin 3,
      NSEMaxwell.Classical.coordinateDerivative
        (NSEMaxwell.Classical.coordinateDerivative (u z.1) i) i z.2)
    NSEMaxwell.Classical.forwardSpacetime
  exact ContDiffOn.sum (fun i _ =>
    NSEMaxwell.Spacetime.coordinateDerivative_trajectory_smooth
      (NSEMaxwell.Spacetime.coordinateDerivative_trajectory_smooth hu i) i)

theorem forward_divergence_smooth {u : Velocity}
    (hu : NSEMaxwell.Classical.SmoothVelocity u) :
    NSEMaxwell.Classical.SmoothPressure
      (fun t => NSEMaxwell.Classical.divergence (u t)) := by
  have hc (i : Fin 3) :=
    (contDiffOn_piLp 2).mp
      (NSEMaxwell.Spacetime.coordinateDerivative_trajectory_smooth hu i) i
  simpa [NSEMaxwell.Classical.SmoothPressure, NSEMaxwell.Classical.divergence,
    Fin.sum_univ_succ, add_assoc] using ((hc 0).add (hc 1)).add (hc 2)

def forwardResidual (ν : ℝ) (u : Velocity) (p : Pressure) : Velocity :=
  fun t x => NSEMaxwell.Classical.timeDerivative u t x +
    NSEMaxwell.Classical.convection (u t) x +
    NSEMaxwell.Classical.gradient (p t) x -
    ν • NSEMaxwell.Classical.laplacian (u t) x

theorem forwardResidual_smooth {ν : ℝ} {u : Velocity} {p : Pressure}
    (hu : NSEMaxwell.Classical.SmoothVelocity u)
    (hp : NSEMaxwell.Classical.SmoothPressure p) :
    NSEMaxwell.Classical.SmoothVelocity (forwardResidual ν u p) := by
  exact (((NSEMaxwell.Spacetime.timeDerivative_smooth hu).add
    (forward_convection_smooth hu)).add (forward_gradient_smooth hp)).sub
    ((forward_laplacian_smooth hu).const_smul ν)

theorem forward_residual_zero_of_positive
    {ν : ℝ} {u : Velocity} {p : Pressure}
    (hu : NSEMaxwell.Classical.SmoothVelocity u)
    (hp : NSEMaxwell.Classical.SmoothPressure p)
    (heq : ∀ t : ℝ, 0 < t → ∀ x : Vec, nseResidual ν u p t x = 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, forwardResidual ν u p t x = 0 := by
  have hz : ∀ z ∈ positiveSpacetime, forwardResidual ν u p z.1 z.2 = 0 := by
    intro z hz
    unfold forwardResidual
    rw [← nse_gr_calculus_agree_on_positive_time ν u p hz z.2]
    exact heq z.1 hz z.2
  have hclosed := continuousOn_forward_eq_zero_of_positive
    (forwardResidual_smooth hu hp).continuousOn hz
  intro t ht x
  exact hclosed (t, x) ht

theorem forward_divergence_zero_of_positive {u : Velocity}
    (hu : NSEMaxwell.Classical.SmoothVelocity u)
    (hdiv : ∀ t : ℝ, 0 < t → ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0 := by
  have hclosed := continuousOn_forward_eq_zero_of_positive
    (forward_divergence_smooth hu).continuousOn (fun z hz => hdiv z.1 hz z.2)
  intro t ht x
  exact hclosed (t, x) ht

theorem nssolution_of_positive_time_equations
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (hu : NSEMaxwell.Classical.SmoothVelocity u)
    (hp : NSEMaxwell.Classical.SmoothPressure p)
    (huper : NSEMaxwell.Classical.PeriodicVelocity u)
    (hpper : NSEMaxwell.Classical.PeriodicPressure p)
    (hdiv : ∀ t : ℝ, 0 < t → ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0)
    (heq : ∀ t : ℝ, 0 < t → ∀ x : Vec, nseResidual ν u p t x = 0)
    (hinitial : u 0 = a) : NSEMaxwell.Classical.NSSolution ν a u p := by
  refine {
    velocity_smooth := hu
    pressure_smooth := hp
    velocity_periodic := huper
    pressure_periodic := hpper
    divergence_free := forward_divergence_zero_of_positive hu hdiv
    equation := ?_
    initial := hinitial }
  intro t ht x
  exact sub_eq_zero.mp (forward_residual_zero_of_positive hu hp heq t ht x)

theorem nssolution_initial_right_derivative
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) (x : Vec) :
    NSEMaxwell.Classical.timeDerivative u 0 x =
      ν • NSEMaxwell.Classical.laplacian a x -
        NSEMaxwell.Classical.convection a x -
        NSEMaxwell.Classical.gradient (p 0) x := by
  have heq := h.equation 0 le_rfl x
  rw [h.initial] at heq
  apply eq_sub_iff_add_eq.mpr
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_assoc, add_left_comm, add_comm] using heq

end
end NSEGR.Strengthening
