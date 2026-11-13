import FourierHodgeLaws.ParameterIntegral

/-!
Exact H3 assembly from parameter smoothing of the frozen inverse Laplacians.
The kinetic mean and divergence assertions are proved from actual calculus.
The parameter-smoothing assumptions are explicit until the Fourier-jet module
supplies their native proofs.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge NSEMaxwell.Spacetime
open NSEMaxwell.FourierPeriodic
open scoped ContDiff

noncomputable section

theorem canonicalVelocity_smooth_of_vectorL_smooth
    (m : Vec) (B : Velocity)
    (hL : SmoothVelocity (fun t => vectorL (B t))) :
    SmoothVelocity (canonicalVelocity m B) := by
  exact contDiffOn_const.add (curl_trajectory_smooth hL)

theorem canonicalVelocity_divergence_free_of_vectorL_smooth
    (m : Vec) (B : Velocity)
    (hL : SmoothVelocity (fun t => vectorL (B t))) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      NSEMaxwell.Classical.divergence (canonicalVelocity m B t) x = 0 := by
  intro t ht x
  have hs : ContDiff ℝ ∞ (vectorL (B t)) := velocity_slice_smooth hL ht
  have hd := congrFun (NSEMaxwell.CurlCurl.divergence_curl hs) x
  change NSEMaxwell.Classical.divergence
    (fun y => m + spatialCurl (vectorL (B t)) y) x = 0
  simpa only [NSEMaxwell.Classical.divergence, coordinateDerivative,
    fderiv_const_add, Pi.zero_apply] using hd

theorem canonicalPressure_smooth_of_scalarL_smooth
    (ν : ℝ) (m : Vec) (B : Velocity)
    (hU : SmoothVelocity (canonicalVelocity m B))
    (hH : SmoothPressure (fun t => scalarL (Q ν m (B t)))) :
    SmoothPressure (canonicalPressureTrajectory ν m B) := by
  have hkin : SmoothPressure (fun t x => ‖canonicalVelocity m B t x‖ ^ 2) :=
    hU.norm_sq ℝ
  have hmean := kineticMean_trajectory_smooth (canonicalVelocity m B) hU
  exact (hH.sub (hkin.div_const 2)).add (hmean.div_const 2)

theorem canonical_smoothness_of_parameter_smoothing
    (hVL : ∀ (B : Velocity), SmoothVelocity B → PeriodicVelocity B →
      SmoothVelocity (fun t => vectorL (B t)))
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t)))
    (ν c : ℝ) (m : Vec) (B : Velocity)
    (hB : SmoothVelocity B) (hp : PeriodicVelocity B) :
    NSEMaxwell.Bridge.CanonicalSmoothness ν c m B := by
  have hL := hVL B hB hp
  have hU := canonicalVelocity_smooth_of_vectorL_smooth m B hL
  have hQ := NSEMaxwell.CanonicalSmoothness.canonical_charge_smooth ν m B hB hU
  have hQp := canonicalCharge_periodic ν m hp
  have hH := hSL (canonicalCharge ν m B) hQ hQp
  exact {
    velocity_smooth := hU
    pressure_smooth := canonicalPressure_smooth_of_scalarL_smooth ν m B hU hH
    velocity_divergence_free :=
      canonicalVelocity_divergence_free_of_vectorL_smooth m B hL
  }

theorem H3_of_parameter_smoothing
    (hVL : ∀ (B : Velocity), SmoothVelocity B → PeriodicVelocity B →
      SmoothVelocity (fun t => vectorL (B t)))
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t)))
    (ν c : ℝ) (m : Vec) (B : Velocity) (hB : MagneticPath B) :
    NSEMaxwell.Bridge.CanonicalSmoothness ν c m B :=
  canonical_smoothness_of_parameter_smoothing hVL hSL ν c m B hB.smooth hB.periodic

end

end NSEMaxwell.HodgeProof
