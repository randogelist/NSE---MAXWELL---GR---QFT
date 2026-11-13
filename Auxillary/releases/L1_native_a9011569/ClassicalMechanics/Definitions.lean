import ClassicalMechanics.Stress

/-!
# Concrete Newtonian continuum endpoint

The stress and its divergence are the actual differential operators of
`ClassicalMechanics.Stress`. The global trajectory scope is exactly the existing
`NSEMaxwell.Classical.NSSolution` scope: arbitrary velocity mean, arbitrary
periodic pressure gauge, joint smoothness on the closed nonnegative half-space.

The endpoint is the local Cauchy momentum balance. Material flow, moving-region
momentum balance, and the Lagrange-d'Alembert formulation are distinct later
endpoints; none is assumed by this structure.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

/-- Actual Eulerian material acceleration. -/
def materialAcceleration (u : Velocity) (t : ℝ) (x : Vec) : Vec :=
  timeDerivative u t x + convection (u t) x

/-- Smooth incompressible Newtonian Cauchy balance on every nonnegative time. -/
structure NewtonianSolution (ν : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : SmoothVelocity u
  pressure_smooth : SmoothPressure p
  velocity_periodic : PeriodicVelocity u
  pressure_periodic : PeriodicPressure p
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    NSEMaxwell.Classical.divergence (u t) x = 0
  momentum_balance : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    materialAcceleration u t x =
      tensorDivergence (newtonianStress ν (u t) (p t)) x
  initial : u 0 = a

/-- The actual arbitrary-mean global Newtonian existence proposition. -/
def NewtonianB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a →
    ∃ (u : Velocity) (p : Pressure), NewtonianSolution ν a u p

/-- Concrete global equivalence target; this definition is not its proof. -/
def GlobalExactEquivalence : Prop :=
  ∀ ν : ℝ, 0 < ν → (FeffermanB ν ↔ NewtonianB ν)

end

end ClassicalMechanics
