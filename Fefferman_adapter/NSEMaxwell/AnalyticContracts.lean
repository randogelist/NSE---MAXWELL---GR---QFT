import NSEMaxwell.Negation
import NSEMaxwell.Lamb
import NSEMaxwell.Pressure
import NSEMaxwell.Ampere
import NSEMaxwell.ConstantPaths
import NSEMaxwell.CurlCurl

/-!
# Shared concrete analytic contracts and initial-data adapters

Every field and operator below is the concrete object defined in Classical.lean.
`PeriodicAnalyticLaws` lists unresolved local analytic identities. It contains
neither FeffermanB, MaxwellB, ExactEquivalence, nor a solution-existence map.

The forward and reverse solution constructions consume this common contract
from their separate modules. No inhabitant of PeriodicAnalyticLaws is supplied
here; every analytic premise remains explicit.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical NSEMaxwell.Constitutive
open scoped ContDiff

noncomputable section

/-- Smooth NSEMaxwell.Classical.divergence-free mean-zero magnetic trajectories, including t = 0. -/
structure MagneticPath (B : Velocity) : Prop where
  smooth : SmoothVelocity B
  periodic : PeriodicVelocity B
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (B t) x = 0
  mean_zero : ∀ t : ℝ, 0 ≤ t → spatialMean (B t) = 0

theorem MagneticPath.slice {B : Velocity} (h : MagneticPath B)
    {t : ℝ} (ht : 0 ≤ t) : MagneticData (B t) := by
  exact ⟨⟨velocity_slice_smooth h.smooth ht, h.periodic t ht,
    h.divergence_free t ht⟩, h.mean_zero t ht⟩

theorem MagneticPath.constant (B : Field) (hB : MagneticData B) :
    MagneticPath (fun _ : ℝ => B) := by
  exact ⟨smooth_constant_velocity B hB.smooth,
    periodic_constant_velocity B hB.periodic,
    fun _ _ => hB.divergence_free, fun _ _ => hB.mean_zero⟩

def curlTrajectory (u : Velocity) : Velocity := fun t => spatialCurl (u t)

def momentumResidual (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) : Field :=
  timeDerivative u t + convection (u t) + NSEMaxwell.Classical.gradient (p t) - ν • NSEMaxwell.Classical.laplacian (u t)

def lambField (m : Vec) (B : Field) : Field :=
  fun x => cross (B x) (U m B x)

def kineticPotential (m : Vec) (B : Field) : ScalarField :=
  fun x => ‖U m B x‖ ^ 2 / 2

def headPotential (ν : ℝ) (m : Vec) (B : Field) : ScalarField :=
  scalarL (Q ν m B)

/-- Regularity of explicitly constructed fields; no evolution is assumed. -/
structure CanonicalRegularity (ν c : ℝ) (m : Vec) (B : Velocity) : Prop where
  velocity_smooth : SmoothVelocity (canonicalVelocity m B)
  pressure_smooth : SmoothPressure (canonicalPressureTrajectory ν m B)
  electric_smooth : SmoothVelocity (canonicalElectric ν m B)
  charge_smooth : SmoothPressure (canonicalCharge ν m B)
  current_smooth : SmoothVelocity (canonicalCurrent ν c m B)
  velocity_periodic : PeriodicVelocity (canonicalVelocity m B)
  pressure_periodic : PeriodicPressure (canonicalPressureTrajectory ν m B)
  electric_periodic : PeriodicVelocity (canonicalElectric ν m B)
  charge_periodic : PeriodicPressure (canonicalCharge ν m B)
  current_periodic : PeriodicVelocity (canonicalCurrent ν c m B)
  velocity_divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    NSEMaxwell.Classical.divergence (canonicalVelocity m B t) x = 0

/--
OPEN ANALYTIC PREMISES. Each field is a concrete analytic statement, not a new
axiom declaration. An unconditional root theorem requires a proved inhabitant
of this structure. No such inhabitant is asserted in this repository.
-/
structure PeriodicAnalyticLaws : Prop where
  reconstruct_velocity : ∀ (a : Field), Data a →
    U (spatialMean a) (spatialCurl a) = a
  reconstruct_curl : ∀ (m : Vec) (B : Field), MagneticData B →
    spatialCurl (U m B) = B
  vorticity_regularity : ∀ (u : Velocity),
    SmoothVelocity u → PeriodicVelocity u →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0) →
    MagneticPath (curlTrajectory u)
  canonical_regularity : ∀ (ν c : ℝ) (m : Vec) (B : Velocity),
    MagneticPath B → CanonicalRegularity ν c m B
  mean_conservation : ∀ (ν : ℝ) (u : Velocity) (p : Pressure),
    SmoothVelocity u → SmoothPressure p →
    PeriodicVelocity u → PeriodicPressure p →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0) →
    (∀ t : ℝ, 0 ≤ t → momentumResidual ν u p t = 0) →
    ∀ t : ℝ, 0 ≤ t → spatialMean (u t) = spatialMean (u 0)
  vorticity_residual : ∀ (ν : ℝ) (u : Velocity) (p : Pressure),
    SmoothVelocity u → SmoothPressure p →
    PeriodicVelocity u → PeriodicPressure p →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0) →
    ∀ t : ℝ, 0 ≤ t →
    spatialCurl (momentumResidual ν u p t) =
      timeDerivative (curlTrajectory u) t +
        spatialCurl (fun x => cross (spatialCurl (u t) x) (u t x) +
          ν • spatialCurl (spatialCurl (u t)) x)
  reconstruction_time : ∀ (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    timeDerivative (canonicalVelocity m B) t = K (timeDerivative B t)
  electric_hodge : ∀ (ν : ℝ) (m : Vec) (B : Field), MagneticData B →
    G ν m B + NSEMaxwell.Classical.gradient (headPotential ν m B) = K (spatialCurl (G ν m B))
  electric_time_chain : ∀ (ν : ℝ) (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    timeDerivative (canonicalElectric ν m B) t =
      DG ν m (B t) (timeDerivative B t)

/-- Initial vorticity admissibility follows by applying path regularity to a
constant trajectory. It is not an independent analytic premise. -/
theorem PeriodicAnalyticLaws.curl_data
    (laws : PeriodicAnalyticLaws) (a : Field) (ha : Data a) :
    MagneticData (spatialCurl a) := by
  have h := laws.vorticity_regularity (fun _ : ℝ => a)
    (smooth_constant_velocity a ha.smooth)
    (periodic_constant_velocity a ha.periodic)
    (fun _ _ => ha.divergence_free)
  exact h.slice (t := 0) (le_refl 0)

/-- Admissibility of reconstructed initial velocity is a constant-path slice
of the already required canonical regularity endpoint. -/
theorem PeriodicAnalyticLaws.reconstruction_data
    (laws : PeriodicAnalyticLaws) (m : Vec) (B : Field) (hB : MagneticData B) :
    Data (U m B) := by
  have h := laws.canonical_regularity 0 0 m (fun _ : ℝ => B)
    (MagneticPath.constant B hB)
  exact ⟨velocity_slice_smooth h.velocity_smooth (t := 0) (le_refl 0),
    h.velocity_periodic 0 (le_refl 0), h.velocity_divergence_free 0 (le_refl 0)⟩

/-- Mean reconstruction follows from the two Hodge inverse identities by
pointwise cancellation; it is not an additional integral premise. -/
theorem PeriodicAnalyticLaws.reconstruct_mean
    (laws : PeriodicAnalyticLaws) (m : Vec) (B : Field) (hB : MagneticData B) :
    spatialMean (U m B) = m := by
  have h := laws.reconstruct_velocity (U m B) (laws.reconstruction_data m B hB)
  rw [laws.reconstruct_curl m B hB] at h
  have hx := congrFun h (0 : Vec)
  change spatialMean (U m B) + K B 0 = m + K B 0 at hx
  exact add_right_cancel hx

end

end NSEMaxwell.Bridge
