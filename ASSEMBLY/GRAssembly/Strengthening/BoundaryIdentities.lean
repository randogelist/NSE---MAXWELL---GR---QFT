import GRAssembly.Strengthening.BoundaryEndpoint
import GRAssembly.Strengthening.InitialPDE

/-!
# Actual boundary pressure and initial projected NSE identities

The velocity-only trace construction yields an actual smooth forward NSE
solution. Its pressure is the literal normalized quadratic Poisson pressure
at every nonnegative time, including the initial time. Its initial right
time derivative is the native projected physical NSE vector field.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem profileBoundary_is_nssolution {ν : ℝ} {a : Field}
    (ha : NSEMaxwell.Classical.Data a) (r : PositiveProfileRepresentative ν a) :
    NSEMaxwell.Classical.NSSolution ν a
      (profileBoundaryVelocity r) (profileBoundaryPressure r) :=
  smoothProfileExtension_is_nssolution r (profileBoundaryVelocity r) (profileBoundaryPressure r)
    (profileBoundaryVelocity_smooth r) (profileBoundaryPressure_smooth r)
    (profileBoundaryVelocity_initial ha r)
    (fun _ ht => ⟨profileBoundaryVelocity_positive r ht, profileBoundaryPressure_positive r ht⟩)

theorem profileBoundaryPressure_origin {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (t : ℝ) :
    profileBoundaryPressure r t 0 = 0 :=
  normalizedSobolevPressure_origin (profileSobolevCurve r) t

theorem profileBoundaryPressure_eq_quadratic {ν : ℝ} {a : Field}
    (ha : NSEMaxwell.Classical.Data a) (r : PositiveProfileRepresentative ν a)
    {t : ℝ} (ht : 0 ≤ t) :
    profileBoundaryPressure r t = normalizedQuadraticPressure (profileBoundaryVelocity r t) := by
  have h := nssolution_normalized_pressure_eq_quadraticPoisson
    (profileBoundary_is_nssolution ha r) ht
  funext x
  simpa only [originNormalize, profileBoundaryPressure_origin, sub_zero] using congrFun h x

theorem profileBoundaryPressure_initial {ν : ℝ} {a : Field}
    (ha : NSEMaxwell.Classical.Data a) (r : PositiveProfileRepresentative ν a) :
    profileBoundaryPressure r 0 = normalizedQuadraticPressure a :=
  nssolution_initial_normalized_pressure (profileBoundary_is_nssolution ha r)
    (profileBoundaryPressure_origin r 0)

theorem profileBoundaryVelocity_projected_equation {ν : ℝ} {a : Field}
    (ha : NSEMaxwell.Classical.Data a) (r : PositiveProfileRepresentative ν a)
    {t : ℝ} (ht : 0 ≤ t) :
    NSEMaxwell.Classical.timeDerivative (profileBoundaryVelocity r) t +
        leray (tensorDivergence (fun x => velocityOuter (profileBoundaryVelocity r t x))) =
      ν • laplacian (profileBoundaryVelocity r t) :=
  nssolution_projected_equation (profileBoundary_is_nssolution ha r) ht

theorem profileBoundaryVelocity_initial_right_derivative_leray {ν : ℝ} {a : Field}
    (ha : NSEMaxwell.Classical.Data a) (r : PositiveProfileRepresentative ν a) :
    NSEMaxwell.Classical.timeDerivative (profileBoundaryVelocity r) 0 =
      ν • laplacian a - leray (tensorDivergence (fun x => velocityOuter (a x))) :=
  nssolution_initial_right_derivative_leray (profileBoundary_is_nssolution ha r)

end
end NSEGR.Strengthening
