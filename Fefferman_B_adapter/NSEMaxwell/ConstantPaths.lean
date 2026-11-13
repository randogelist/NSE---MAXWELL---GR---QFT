import NSEMaxwell.Kinematics

/-!
# Constant-in-time trajectories

A smooth spatial field defines a jointly smooth trajectory on the closed
nonnegative-time domain by composition with the spatial projection. No
additional temporal regularity premise is required.
-/

set_option autoImplicit false

open scoped ContDiff

namespace NSEMaxwell.Classical

noncomputable section

theorem smooth_constant_velocity (a : Field) (ha : ContDiff ℝ ∞ a) :
    SmoothVelocity (fun _ : ℝ => a) := by
  exact (ha.comp contDiff_snd).contDiffOn

theorem smooth_constant_pressure (p : ScalarField) (hp : ContDiff ℝ ∞ p) :
    SmoothPressure (fun _ : ℝ => p) := by
  exact (hp.comp contDiff_snd).contDiffOn

theorem periodic_constant_velocity (a : Field) (ha : SpatialPeriodic a) :
    PeriodicVelocity (fun _ : ℝ => a) := by
  intro _ _
  exact ha

theorem periodic_constant_pressure (p : ScalarField) (hp : SpatialPeriodic p) :
    PeriodicPressure (fun _ : ℝ => p) := by
  intro _ _
  exact hp

end

end NSEMaxwell.Classical
