import GRAssembly.Strengthening.SourceCarrier
import GRAssembly.Strengthening.PositivePDE

/-!
The exact normalized forward source is determined by its positive-time
velocity. Pressure equality follows from the actual momentum equation and
origin normalization. Continuity supplies the initial hypersurface values.
No positive-time analyticity or pressure-recovery premise is required.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped ContDiff Topology

namespace NSEGR.Strengthening
noncomputable section

theorem smooth_velocity_eq_forward_of_positive {u v : Velocity}
    (hu : NSEMaxwell.Classical.SmoothVelocity u)
    (hv : NSEMaxwell.Classical.SmoothVelocity v)
    (heq : ∀ t : ℝ, 0 < t → u t = v t) :
    ∀ t : ℝ, 0 ≤ t → u t = v t := by
  have hd : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2 - v z.1 z.2)
      NSEMaxwell.Classical.forwardSpacetime := hu.continuousOn.sub hv.continuousOn
  have hc := continuousOn_forward_eq_zero_of_positive hd
    (fun z hz => sub_eq_zero.mpr (congrFun (heq z.1 hz) z.2))
  intro t ht
  funext x
  exact sub_eq_zero.mp (hc (t, x) ht)

theorem smooth_pressure_eq_forward_of_positive {p q : Pressure}
    (hp : NSEMaxwell.Classical.SmoothPressure p)
    (hq : NSEMaxwell.Classical.SmoothPressure q)
    (heq : ∀ t : ℝ, 0 < t → p t = q t) :
    ∀ t : ℝ, 0 ≤ t → p t = q t := by
  have hd : ContinuousOn (fun z : ℝ × Vec => p z.1 z.2 - q z.1 z.2)
      NSEMaxwell.Classical.forwardSpacetime := hp.continuousOn.sub hq.continuousOn
  have hc := continuousOn_forward_eq_zero_of_positive hd
    (fun z hz => sub_eq_zero.mpr (congrFun (heq z.1 hz) z.2))
  intro t ht
  funext x
  exact sub_eq_zero.mp (hc (t, x) ht)

theorem nssolution_gradient_eq_of_eventuallyEq
    {ν t : ℝ} {a b : Field} {u v : Velocity} {p q : Pressure}
    (hn : NSEMaxwell.Classical.NSSolution ν a u p)
    (hm : NSEMaxwell.Classical.NSSolution ν b v q)
    (ht : 0 < t) (hV : u =ᶠ[𝓝 t] v) : gradient (p t) = gradient (q t) := by
  have hs : u t = v t := hV.eq_of_nhds
  funext x
  have hdt : NSEMaxwell.Classical.timeDerivative u t x =
      NSEMaxwell.Classical.timeDerivative v t x := by
    rw [timeDerivative_eq_localTimeDerivative u ht x,
      timeDerivative_eq_localTimeDerivative v ht x]
    have hevent : (fun s : ℝ => u s x) =ᶠ[𝓝 t] (fun s : ℝ => v s x) :=
      hV.mono (fun s hs' => congrFun hs' x)
    exact hevent.deriv_eq
  have hp := hn.equation t ht.le x
  have hq := hm.equation t ht.le x
  rw [hdt, hs] at hp
  exact add_left_cancel (hp.trans hq.symm)

theorem nssolution_originNormalize_eq_of_eventuallyEq
    {ν t : ℝ} {a b : Field} {u v : Velocity} {p q : Pressure}
    (hn : NSEMaxwell.Classical.NSSolution ν a u p)
    (hm : NSEMaxwell.Classical.NSSolution ν b v q)
    (ht : 0 < t) (hV : u =ᶠ[𝓝 t] v) :
    originNormalize p t = originNormalize q t := by
  exact originNormalize_eq_of_gradient_eq
    ((NSEMaxwell.Classical.pressure_slice_smooth hn.pressure_smooth ht.le).differentiable
      (by simp))
    ((NSEMaxwell.Classical.pressure_slice_smooth hm.pressure_smooth ht.le).differentiable
      (by simp))
    (nssolution_gradient_eq_of_eventuallyEq hn hm ht hV)

theorem nssolution_normalized_pressure_eq_of_positive_velocity_eq
    {ν : ℝ} {a b : Field} {u v : Velocity} {p q : Pressure}
    (hn : NSEMaxwell.Classical.NSSolution ν a u p)
    (hm : NSEMaxwell.Classical.NSSolution ν b v q)
    (hnp : ∀ t : ℝ, 0 ≤ t → p t 0 = 0)
    (hmp : ∀ t : ℝ, 0 ≤ t → q t 0 = 0)
    (hV : ∀ t : ℝ, 0 < t → u t = v t) :
    ∀ t : ℝ, 0 ≤ t → p t = q t := by
  apply smooth_pressure_eq_forward_of_positive hn.pressure_smooth hm.pressure_smooth
  intro t ht
  have hev : u =ᶠ[𝓝 t] v := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact hV s hs
  have hp := nssolution_originNormalize_eq_of_eventuallyEq hn hm ht hev
  funext x
  have hx := congrFun hp x
  simpa only [originNormalize, hnp t ht.le, hmp t ht.le, sub_zero] using hx

theorem NormalizedForwardTrajectory.eq_of_positive_velocity_eq
    {ν : ℝ} {a : Field} (s r : NormalizedForwardTrajectory ν a)
    (hV : ∀ t : ℝ, ∀ ht : 0 < t, s.velocity t ht.le = r.velocity t ht.le) :
    s = r := by
  have hpos : ∀ t : ℝ, 0 < t → s.totalVelocity t = r.totalVelocity t := by
    intro t ht
    rw [s.totalVelocity_eq ht.le, r.totalVelocity_eq ht.le]
    exact hV t ht
  have hv := smooth_velocity_eq_forward_of_positive
    s.solution.velocity_smooth r.solution.velocity_smooth hpos
  have hp := nssolution_normalized_pressure_eq_of_positive_velocity_eq
    s.solution r.solution
    (fun t ht => s.totalPressure_zero ht) (fun t ht => r.totalPressure_zero ht) hpos
  apply (NormalizedForwardTrajectory.eq_iff_forward s r).mpr
  intro t ht
  constructor
  · simpa only [s.totalVelocity_eq ht, r.totalVelocity_eq ht] using hv t ht
  · simpa only [s.totalPressure_eq ht, r.totalPressure_eq ht] using hp t ht

theorem NormalizedForwardTrajectory.eq_iff_positive_velocity
    {ν : ℝ} {a : Field} (s r : NormalizedForwardTrajectory ν a) :
    s = r ↔ ∀ t : ℝ, ∀ ht : 0 < t, s.velocity t ht.le = r.velocity t ht.le := by
  constructor
  · rintro rfl
    exact fun _ _ => rfl
  · exact NormalizedForwardTrajectory.eq_of_positive_velocity_eq s r

end
end NSEGR.Strengthening
