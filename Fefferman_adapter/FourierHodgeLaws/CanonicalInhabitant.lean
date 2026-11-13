import FourierHodgeLaws.CanonicalFromScalar
import FourierHodgeLaws.ParameterSmoothing

/-!
The exact H3 endpoint assembled from actual scalar parameter smoothing.
No inverse-Laplacian or regularity admission remains in the theorem types.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge

noncomputable section

theorem canonical_smoothness (ν c : ℝ) (m : Vec) (B : Velocity)
    (hB : SmoothVelocity B) (hp : PeriodicVelocity B) :
    NSEMaxwell.Bridge.CanonicalSmoothness ν c m B :=
  canonical_smoothness_of_scalar_parameter_smoothing
    (fun _ hf hper => scalarL_trajectory_smooth hf hper) ν c m B hB hp

theorem h3_canonical_smoothness (ν c : ℝ) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) : NSEMaxwell.Bridge.CanonicalSmoothness ν c m B :=
  canonical_smoothness ν c m B hB.smooth hB.periodic

end

end NSEMaxwell.HodgeProof
