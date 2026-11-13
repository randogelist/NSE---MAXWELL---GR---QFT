import NSEMaxwell.AnalyticBridge
import NSEMaxwell.LocalEvolution
import NSEMaxwell.MeanConservation
import NSEMaxwell.FourierPeriodic
import NSEMaxwell.CanonicalSmoothness

/-!
# Reduction to the remaining concrete Fourier and Hodge analysis

Five previously independent endpoints are now derived: vorticity regularity,
conservation of the velocity mean, the vorticity residual, temporal
reconstruction, and the electric chain rule. All use actual derivatives and
actual cube integrals. The original concrete propositions are unchanged.

`FourierHodgeLaws` remains an explicit unresolved premise. In particular this
file does not supply Fourier convergence, inversion, or smooth parameter
dependence for the operators in Classical.lean.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration
open NSEMaxwell.FourierPeriodic NSEMaxwell.TemporalMean
open scoped ContDiff

noncomputable section

/-- The five canonical periodicity conclusions are already proved concretely. -/
structure CanonicalSmoothness (ν c : ℝ) (m : Vec) (B : Velocity) : Prop where
  velocity_smooth : SmoothVelocity (canonicalVelocity m B)
  pressure_smooth : SmoothPressure (canonicalPressureTrajectory ν m B)
  velocity_divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    NSEMaxwell.Classical.divergence (canonicalVelocity m B t) x = 0

/-- Four named analytic endpoints; no inhabitant is claimed. -/
structure FourierHodgeLaws : Prop where
  reconstruct_velocity : ∀ (a : Field), Data a →
    U (spatialMean a) (spatialCurl a) = a
  reconstruct_curl : ∀ (m : Vec) (B : Field), MagneticData B →
    spatialCurl (U m B) = B
  canonical_smoothness : ∀ (ν c : ℝ) (m : Vec) (B : Velocity),
    MagneticPath B → CanonicalSmoothness ν c m B
  electric_hodge : ∀ (ν : ℝ) (m : Vec) (B : Field), MagneticData B →
    G ν m B + NSEMaxwell.Classical.gradient (headPotential ν m B) =
      K (spatialCurl (G ν m B))

/-- Curl regularity, periodicity, divergence, and zero mean need no Hodge premise. -/
theorem vorticity_regularity_proved
    (u : Velocity) (hu : SmoothVelocity u) (hp : PeriodicVelocity u) :
    MagneticPath (curlTrajectory u) := by
  refine ⟨curl_trajectory_smooth hu, ?_, ?_, ?_⟩
  · intro t ht
    exact spatialCurl_periodic (hp t ht)
  · intro t ht x
    exact congrFun (NSEMaxwell.CurlCurl.divergence_curl
      (velocity_slice_smooth hu ht)) x
  · intro t ht
    exact spatialMean_curl_zero (velocity_slice_smooth hu ht) (hp t ht)

theorem FourierHodgeLaws.canonical_regularity
    (laws : FourierHodgeLaws) (ν c : ℝ) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) : CanonicalRegularity ν c m B := by
  have h := laws.canonical_smoothness ν c m B hB
  have hU : ∀ (m' : Vec) (B' : Velocity), MagneticPath B' →
      SmoothVelocity (canonicalVelocity m' B') :=
    fun m' B' hB' => (laws.canonical_smoothness 0 0 m' B' hB').velocity_smooth
  exact {
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    electric_smooth := NSEMaxwell.CanonicalSmoothness.canonical_electric_smooth
      ν m B hB.smooth h.velocity_smooth
    charge_smooth := NSEMaxwell.CanonicalSmoothness.canonical_charge_smooth
      ν m B hB.smooth h.velocity_smooth
    current_smooth := NSEMaxwell.CanonicalSmoothness.canonical_current_smooth_of_velocity_smoothing
      hU ν c m B hB
    velocity_periodic := canonicalVelocity_periodic m B
    pressure_periodic := canonicalPressureTrajectory_periodic ν m B
    electric_periodic := canonicalElectric_periodic ν m hB.periodic
    charge_periodic := canonicalCharge_periodic ν m hB.periodic
    current_periodic := canonicalCurrent_periodic ν c m hB.periodic
    velocity_divergence_free := h.velocity_divergence_free }

theorem FourierHodgeLaws.reconstruction_data
    (laws : FourierHodgeLaws) (m : Vec) (B : Field) (hB : MagneticData B) :
    Data (U m B) := by
  have h := laws.canonical_regularity 0 0 m (fun _ : ℝ => B)
    (MagneticPath.constant B hB)
  exact ⟨velocity_slice_smooth h.velocity_smooth (t := 0) (le_refl 0),
    h.velocity_periodic 0 (le_refl 0), h.velocity_divergence_free 0 (le_refl 0)⟩

theorem FourierHodgeLaws.reconstruct_mean
    (laws : FourierHodgeLaws) (m : Vec) (B : Field) (hB : MagneticData B) :
    spatialMean (U m B) = m := by
  have h := laws.reconstruct_velocity (U m B) (laws.reconstruction_data m B hB)
  rw [laws.reconstruct_curl m B hB] at h
  have hx := congrFun h (0 : Vec)
  change spatialMean (U m B) + K B 0 = m + K B 0 at hx
  exact add_right_cancel hx

/-- Temporal reconstruction follows from spatial inversion and concrete calculus. -/
theorem FourierHodgeLaws.reconstruction_time
    (laws : FourierHodgeLaws) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) {t : ℝ} (ht : 0 ≤ t) :
    timeDerivative (canonicalVelocity m B) t = K (timeDerivative B t) := by
  have hreg := laws.canonical_regularity 0 0 m B hB
  have hdata : Data (timeDerivative (canonicalVelocity m B) t) := {
    smooth := velocity_slice_smooth (timeDerivative_smooth hreg.velocity_smooth) ht
    periodic := timeDerivative_periodic hreg.velocity_periodic t ht
    divergence_free := timeDerivative_divergence_zero hreg.velocity_smooth
      hreg.velocity_divergence_free ht }
  have hmean : spatialMean (timeDerivative (canonicalVelocity m B) t) = 0 :=
    timeDerivative_mean_zero_of_constant_mean hreg.velocity_smooth m
      (fun s hs => laws.reconstruct_mean m (B s) (hB.slice hs)) ht
  have hcurl : spatialCurl (timeDerivative (canonicalVelocity m B) t) =
      timeDerivative B t := by
    rw [← timeDerivative_curl_commute hreg.velocity_smooth ht]
    exact timeDerivative_congr_field
      (fun s hs => laws.reconstruct_curl m (B s) (hB.slice hs)) ht
  have h := laws.reconstruct_velocity
    (timeDerivative (canonicalVelocity m B) t) hdata
  rw [hmean, hcurl] at h
  funext x
  have hx := congrFun h.symm x
  change timeDerivative (canonicalVelocity m B) t x =
    (0 : Vec) + K (timeDerivative B t) x at hx
  simpa only [zero_add] using hx

/-- Actual mean conservation, including the unrestricted harmonic velocity mode. -/
theorem mean_conservation_proved
    (ν : ℝ) (u : Velocity) (p : Pressure)
    (hu : SmoothVelocity u) (hp : SmoothPressure p)
    (huper : PeriodicVelocity u) (hpper : PeriodicPressure p)
    (hdiv : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0)
    (hres : ∀ t : ℝ, 0 ≤ t → momentumResidual ν u p t = 0) :
    ∀ t : ℝ, 0 ≤ t → spatialMean (u t) = spatialMean (u 0) := by
  apply mean_conservation_of_equation ν u p hu hp huper hpper hdiv
  intro t ht x
  exact sub_eq_zero.mp (congrFun (hres t ht) x)

/-- The complete original analytic-law package is derived from four remaining endpoints. -/
theorem FourierHodgeLaws.toPeriodicAnalyticLaws
    (laws : FourierHodgeLaws) : PeriodicAnalyticLaws := by
  refine {
    reconstruct_velocity := laws.reconstruct_velocity
    reconstruct_curl := laws.reconstruct_curl
    vorticity_regularity := ?_
    canonical_regularity := laws.canonical_regularity
    mean_conservation := mean_conservation_proved
    vorticity_residual := ?_
    reconstruction_time := ?_
    electric_hodge := laws.electric_hodge
    electric_time_chain := ?_ }
  · intro u hu hp _
    exact vorticity_regularity_proved u hu hp
  · intro ν u p hu hp _ _ hdiv t ht
    exact NSEMaxwell.LocalEvolution.vorticity_residual ν u p hu hp hdiv ht
  · intro m B hB t ht
    exact laws.reconstruction_time m B hB ht
  · intro ν m B hB t ht
    exact NSEMaxwell.LocalEvolution.electric_time_chain_of_reconstruction ν m B
      hB.smooth (laws.canonical_regularity ν 0 m B hB).velocity_smooth ht
      (laws.reconstruction_time m B hB ht)

theorem exact_equivalence_of_fourierHodgeLaws
    (laws : FourierHodgeLaws) : ExactEquivalence :=
  exact_equivalence_of_periodicAnalyticLaws laws.toPeriodicAnalyticLaws

end

end NSEMaxwell.Bridge
