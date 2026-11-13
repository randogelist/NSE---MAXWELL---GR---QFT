import MaxwellEndpoint.Constitutive

/-!
Exact native constrained-Maxwell solution predicate and global-existence proposition.
A proposition definition supplies no arbitrary-data existence proof.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.Classical

noncomputable section

/-- Constrained Maxwell system with precisely the induced electric field,
charge, and current. Only `m` and `B₀` are independent initial data. -/
structure MaxwellSolution (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity) : Prop where
  magnetic_smooth : SmoothVelocity B
  electric_smooth : SmoothVelocity E
  charge_smooth : SmoothPressure ρ
  current_smooth : SmoothVelocity J
  magnetic_periodic : PeriodicVelocity B
  electric_periodic : PeriodicVelocity E
  charge_periodic : PeriodicPressure ρ
  current_periodic : PeriodicVelocity J
  magnetic_mean_zero : ∀ t : ℝ, 0 ≤ t → spatialMean (B t) = 0
  magnetic_gauss : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (B t) x = 0
  faraday : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative B t x + spatialCurl (E t) x = 0
  electric_gauss : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    divergence (E t) x = ρ t x
  ampere : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative E t x - c ^ 2 • spatialCurl (B t) x = -J t x
  constitutive_electric : ∀ t : ℝ, 0 ≤ t → E t = G ν m (B t)
  constitutive_charge : ∀ t : ℝ, 0 ≤ t → ρ t = Q ν m (B t)
  constitutive_current : ∀ t : ℝ, 0 ≤ t → J t = current ν c m (B t)
  initial : B 0 = B₀

/-- Global constrained-Maxwell existence for arbitrary mean and magnetic datum. -/
def MaxwellB (ν c : ℝ) : Prop :=
  ∀ (m : Vec) (B₀ : Field), MagneticData B₀ →
    ∃ (B E : Velocity) (ρ : Pressure) (J : Velocity),
      MaxwellSolution ν c m B₀ B E ρ J

end

end NSEMaxwell.Classical
