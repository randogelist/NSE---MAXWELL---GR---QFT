import GRAssembly.Strengthening.PressureIdentification

/-!
G35 boundary identities for the actual right-time NSE. The pressure is the
native origin-normalized quadratic Poisson formula and the projected RHS
uses the native Leray operator. The spatial constant velocity mode is retained.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace NSEGR.Strengthening
noncomputable section

theorem gradient_neg_native (p : ScalarField) : gradient (-p) = -gradient p := by
  funext x
  apply PiLp.ext
  intro i
  change fderiv ℝ (fun y : Vec => -p y) x (unitVector i) =
    -(fderiv ℝ p x (unitVector i))
  simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply]

theorem normalizedQuadraticPressure_gradient (v : Field) :
    gradient (normalizedQuadraticPressure v) =
      -gradient (poissonInverse
        (divergence (tensorDivergence (fun x => velocityOuter (v x))))) := by
  change gradient (fun x => quadraticPoissonPressure v x - quadraticPoissonPressure v 0) = _
  rw [gradient_sub_constant]
  change gradient (poissonInverse
    (-divergence (tensorDivergence (fun x => velocityOuter (v x))))) = _
  rw [Assembly.poissonInverse_neg_native, gradient_neg_native]

theorem normalizedQuadraticPressure_leray_transport (v : Field) :
    tensorDivergence (fun x => velocityOuter (v x)) +
        gradient (normalizedQuadraticPressure v) =
      leray (tensorDivergence (fun x => velocityOuter (v x))) := by
  rw [normalizedQuadraticPressure_gradient]
  funext x
  change tensorDivergence (fun y => velocityOuter (v y)) x +
      -(gradient (poissonInverse
        (divergence (tensorDivergence (fun y => velocityOuter (v y))))) x) =
    tensorDivergence (fun y => velocityOuter (v y)) x -
      gradient (poissonInverse
        (divergence (tensorDivergence (fun y => velocityOuter (v y))))) x
  exact (sub_eq_add_neg _ _).symm

theorem nssolution_projected_equation
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) {t : ℝ} (ht : 0 ≤ t) :
    NSEMaxwell.Classical.timeDerivative u t +
        leray (tensorDivergence (fun x => velocityOuter (u t x))) =
      ν • laplacian (u t) := by
  have htransport : tensorDivergence (fun x => velocityOuter (u t x)) = convection (u t) := by
    funext x
    exact tensorDivergence_velocityOuter_of_divergence_zero
      ((NSEMaxwell.Classical.velocity_slice_smooth h.velocity_smooth ht).differentiable
        (by simp) x) (h.divergence_free t ht x)
  have hnorm : gradient (originNormalize p t) = gradient (p t) :=
    originNormalize_gradient p t
  have hpressure : gradient (p t) = gradient (normalizedQuadraticPressure (u t)) :=
    hnorm.symm.trans (congrArg gradient
      (nssolution_normalized_pressure_eq_quadraticPoisson h ht))
  have heq : NSEMaxwell.Classical.timeDerivative u t + convection (u t) + gradient (p t) =
      ν • laplacian (u t) := funext (h.equation t ht)
  rw [hpressure, ← htransport, add_assoc,
    normalizedQuadraticPressure_leray_transport] at heq
  exact heq

theorem nssolution_initial_right_derivative_leray
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) :
    NSEMaxwell.Classical.timeDerivative u 0 =
      ν • laplacian a - leray (tensorDivergence (fun x => velocityOuter (a x))) := by
  have heq := nssolution_projected_equation h (t := 0) le_rfl
  rw [h.initial] at heq
  exact eq_sub_iff_add_eq.mpr heq

theorem nssolution_initial_originPressure
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) :
    originNormalize p 0 = normalizedQuadraticPressure a := by
  simpa only [h.initial] using
    nssolution_normalized_pressure_eq_quadraticPoisson h (t := 0) le_rfl

theorem nssolution_initial_normalized_pressure
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) (hp0 : p 0 0 = 0) :
    p 0 = normalizedQuadraticPressure a := by
  funext x
  simpa only [originNormalize, hp0, sub_zero] using
    congrFun (nssolution_initial_originPressure h) x

end
end NSEGR.Strengthening
