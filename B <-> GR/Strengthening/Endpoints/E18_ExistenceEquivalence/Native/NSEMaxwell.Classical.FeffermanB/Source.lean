import MaxwellEndpoint

/-!
Exact periodic unforced Navier–Stokes statement and the frozen equivalence target.
Concrete shared geometry and Maxwell definitions are imported from the independent
Maxwell_Endpoint package; all original declaration names and bodies are preserved.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.Classical

noncomputable section

/-- Classical unforced periodic NSE, at every nonnegative time.
Pressure is periodic; arbitrary velocity means and pressure gauges are allowed. -/
structure NSSolution (ν : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : SmoothVelocity u
  pressure_smooth : SmoothPressure p
  velocity_periodic : PeriodicVelocity u
  pressure_periodic : PeriodicPressure p
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + gradient (p t) x =
      ν • laplacian (u t) x
  initial : u 0 = a

/-- Fefferman's periodic unforced existence proposition for fixed viscosity. -/
def FeffermanB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a →
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p

/-- The requested unconditional proposition. This declaration is not a proof. -/
def ExactEquivalence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
    (FeffermanB ν ↔ MaxwellB ν c)

end

end NSEMaxwell.Classical
