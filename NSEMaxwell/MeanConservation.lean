import NSEMaxwell.PeriodicIntegration
import NSEMaxwell.TemporalMean

/-!
# Mean conservation for the concrete periodic NSE

All spatial integral cancellations are proved in PeriodicIntegration. The
time derivative of the compact-cube integral is proved in TemporalMean.
The conclusion includes the right endpoint t = 0 and arbitrary initial mean.
-/

set_option autoImplicit false

namespace NSEMaxwell.PeriodicIntegration

open NSEMaxwell.Classical
open Set MeasureTheory
open scoped ContDiff

noncomputable section

theorem spatialMean_timeDerivative_zero_of_constant_mean
    {u : Velocity} (hu : SmoothVelocity u) (m : Vec)
    (hm : ∀ s : ℝ, 0 ≤ s → spatialMean (u s) = m)
    {t : ℝ} (ht : 0 ≤ t) : spatialMean (timeDerivative u t) = 0 := by
  have hd := NSEMaxwell.TemporalMean.mean_time_hasDerivWithinAt hu ht
  have hc : HasDerivWithinAt (fun s : ℝ => spatialMean (u s)) 0 (Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_const (c := m) (s := Ici (0 : ℝ)) (x := t)).congr_of_mem
      (fun s hs => hm s hs) ht
  exact (hd.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm.trans
    (hc.derivWithin (uniqueDiffOn_Ici 0 t ht))

theorem spatialMean_timeDerivative_zero_of_equation
    (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ)
    (hu : ContDiff ℝ ∞ (u t)) (hp : ContDiff ℝ ∞ (p t))
    (huper : SpatialPeriodic (u t)) (hpper : SpatialPeriodic (p t))
    (hdiv : ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0)
    (heq : ∀ x : Vec,
      timeDerivative u t x + convection (u t) x +
        NSEMaxwell.Classical.gradient (p t) x =
          ν • NSEMaxwell.Classical.laplacian (u t) x) :
    spatialMean (timeDerivative u t) = 0 := by
  have htime : timeDerivative u t = fun x =>
      ν • NSEMaxwell.Classical.laplacian (u t) x -
        convection (u t) x - NSEMaxwell.Classical.gradient (p t) x := by
    funext x
    apply eq_sub_iff_add_eq.mpr
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_assoc, add_left_comm, add_comm] using heq x
  have hL := integrableOn_unitCube_of_continuous (laplacian_smooth hu).continuous
  have hC := integrableOn_unitCube_of_continuous (convection_smooth hu).continuous
  have hP := integrableOn_unitCube_of_continuous (gradient_smooth hp).continuous
  unfold spatialMean
  rw [htime, integral_sub ((hL.smul ν).sub hC) hP,
    integral_sub (hL.smul ν) hC, integral_smul]
  change ν • spatialMean (NSEMaxwell.Classical.laplacian (u t)) -
    spatialMean (convection (u t)) -
      spatialMean (NSEMaxwell.Classical.gradient (p t)) = 0
  rw [spatialMean_laplacian_zero hu huper,
    spatialMean_convection_zero hu huper hdiv,
    spatialMean_gradient_zero hp hpper]
  simp

theorem mean_conservation_of_equation
    (ν : ℝ) (u : Velocity) (p : Pressure)
    (hu : SmoothVelocity u) (hp : SmoothPressure p)
    (huper : PeriodicVelocity u) (hpper : PeriodicPressure p)
    (hdiv : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0)
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      timeDerivative u t x + convection (u t) x +
        NSEMaxwell.Classical.gradient (p t) x =
          ν • NSEMaxwell.Classical.laplacian (u t) x) :
    ∀ t : ℝ, 0 ≤ t → spatialMean (u t) = spatialMean (u 0) := by
  have hd (s : ℝ) (hs : 0 ≤ s) :
      HasDerivWithinAt (fun r : ℝ => spatialMean (u r)) 0 (Ici (0 : ℝ)) s := by
    have hmean := NSEMaxwell.TemporalMean.mean_time_hasDerivWithinAt hu hs
    rw [spatialMean_timeDerivative_zero_of_equation ν u p s
      (velocity_slice_smooth hu hs) (pressure_slice_smooth hp hs)
      (huper s hs) (hpper s hs) (hdiv s hs) (heq s hs)] at hmean
    exact hmean
  have hc : ContinuousOn (fun s : ℝ => spatialMean (u s)) (Ici (0 : ℝ)) :=
    fun s hs => (hd s hs).continuousWithinAt
  intro t ht
  apply constant_of_has_deriv_right_zero
    (hc.mono (fun s hs => hs.1)) ?_ t ⟨ht, le_rfl⟩
  intro s hs
  exact (hd s hs.1).mono (fun r hr => hs.1.trans hr)

end

end NSEMaxwell.PeriodicIntegration
