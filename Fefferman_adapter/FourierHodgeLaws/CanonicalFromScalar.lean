import FourierHodgeLaws.CanonicalSmoothness
import FourierHodgeLaws.CosineMultiplier

/-!
The actual scalar parameter-smoothing theorem suffices for the entire H3 field.
Vector smoothing follows by the proved component identity for the frozen L.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge
open scoped ContDiff

noncomputable section

theorem vectorL_trajectory_smooth_of_scalar_parameter_smoothing
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t)))
    (B : Velocity) (hB : SmoothVelocity B) (hp : PeriodicVelocity B) :
    SmoothVelocity (fun t => vectorL (B t)) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hBi : SmoothPressure (fun t x => B t x i) := (contDiffOn_piLp 2).mp hB i
  have hpi : PeriodicPressure (fun t x => B t x i) := by
    intro t ht x j
    exact congrArg (fun v : Vec => v i) (hp t ht x j)
  apply (hSL (fun t x => B t x i) hBi hpi).congr
  intro z hz
  exact congrFun (vectorL_component (B z.1) (velocity_slice_smooth hB hz)
    (hp z.1 hz) i) z.2

theorem canonical_smoothness_of_scalar_parameter_smoothing
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t)))
    (ν c : ℝ) (m : Vec) (B : Velocity)
    (hB : SmoothVelocity B) (hp : PeriodicVelocity B) :
    NSEMaxwell.Bridge.CanonicalSmoothness ν c m B :=
  canonical_smoothness_of_parameter_smoothing
    (vectorL_trajectory_smooth_of_scalar_parameter_smoothing hSL) hSL ν c m B hB hp

theorem H3_of_scalar_parameter_smoothing
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t)))
    (ν c : ℝ) (m : Vec) (B : Velocity) (hB : MagneticPath B) :
    NSEMaxwell.Bridge.CanonicalSmoothness ν c m B :=
  canonical_smoothness_of_scalar_parameter_smoothing hSL ν c m B hB.smooth hB.periodic

end

end NSEMaxwell.HodgeProof
