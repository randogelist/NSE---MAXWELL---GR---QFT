import SingularClosure.SobolevScaleTimeSmooth
import SingularClosure.SobolevSpacetimeSmooth
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.Order.LeftRight

/-!
# Boundary closure for actual compatible Sobolev coefficient curves

These are the G31--G33 composition interfaces. The positive-time derivative
is a norm derivative in the actual `TorusSobolev` space. Deriving that input
from the physical NSE trajectory is the separate G30 obligation; it is not
inferred from coefficientwise differentiability or an axiom audit.

No mean-zero, smallness, AX6, pressure trace, or temporal trace is required.
The exact spatial trace and the positive-time differential equation imply
the right derivative at zero before the scale regularity theorem is applied.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff
open SingularClosure

namespace NSEGR.Strengthening
noncomputable section

/-- Every Sobolev order uses the same actual Fourier coefficient sequence. -/
def coefficientSobolevCurve (c : ℝ → FourierCoeff)
    (hc : ∀ (m : ℕ) (t : ℝ), Memℓp (sobolevWeightedCoeff m (c t)) 2)
    (m : ℕ) (t : ℝ) : TorusSobolev m :=
  ⟨c t, hc m t⟩

@[simp]
theorem coefficientSobolevCurve_coeff (c : ℝ → FourierCoeff)
    (hc : ∀ (m : ℕ) (t : ℝ), Memℓp (sobolevWeightedCoeff m (c t)) 2)
    (m : ℕ) (t : ℝ) : (coefficientSobolevCurve c hc m t).val = c t := rfl

theorem coefficientSobolevCurve_compatible (c : ℝ → FourierCoeff)
    (hc : ∀ (m : ℕ) (t : ℝ), Memℓp (sobolevWeightedCoeff m (c t)) 2) :
    ∀ (m : ℕ) (t : ℝ),
      (coefficientSobolevCurve c hc m t).val =
        (coefficientSobolevCurve c hc 0 t).val := by
  intro m t
  rfl

/-- Spatial trace plus actual positive-time norm derivatives gives forward continuity. -/
theorem sobolev_forward_continuous
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (F m (U (m + 2) t)) t) :
    ∀ m, ContinuousOn (U m) (Ici (0 : ℝ)) := by
  intro m t ht
  by_cases hzero : t = 0
  · subst t
    exact continuousWithinAt_Ioi_iff_Ici.mp (htrace m)
  · exact (hderiv m t (lt_of_le_of_ne ht (Ne.symm hzero))).continuousAt.continuousWithinAt

/-- The initial right derivative is derived from the spatial trace. -/
theorem sobolev_right_boundary_equation
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hF : ∀ m, Continuous (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (F m (U (m + 2) t)) t)
    (m : ℕ) :
    HasDerivWithinAt (U m) (F m (U (m + 2) 0)) (Ici (0 : ℝ)) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hderiv m t ht).differentiableAt.differentiableWithinAt)
    (htrace m) self_mem_nhdsWithin
  have hlimit : Tendsto (fun t => F m (U (m + 2) t))
      (𝓝[>] (0 : ℝ)) (𝓝 (F m (U (m + 2) 0))) :=
    (hF m).continuousAt.tendsto.comp (htrace (m + 2))
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hderiv m t ht).deriv.symm

/-- The actual within differential equation now holds at every nonnegative time. -/
theorem sobolev_forward_derivative_equation
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hF : ∀ m, Continuous (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (F m (U (m + 2) t)) t) :
    ∀ (m : ℕ) (t : ℝ), t ∈ Ici (0 : ℝ) →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Ici (0 : ℝ)) t := by
  intro m t ht
  by_cases hzero : t = 0
  · subst t
    exact sobolev_right_boundary_equation U F htrace hF hderiv m
  · exact (hderiv m t (lt_of_le_of_ne ht (Ne.symm hzero))).hasDerivWithinAt

/-- The generic scale theorem is used only after its boundary derivative premise is proved. -/
theorem sobolev_forward_time_smooth
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hF : ∀ m, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (F m (U (m + 2) t)) t) :
    ∀ m, ContDiffOn ℝ ∞ (U m) (Ici (0 : ℝ)) :=
  SOBOLEV_SCALE_TIME_SMOOTH U F
    (sobolev_forward_continuous U F htrace hderiv) hF
    (sobolev_forward_derivative_equation U F htrace
      (fun m => (hF m).continuous) hderiv)

/-- Compatible physical Fourier synthesis is jointly smooth through the initial boundary. -/
theorem sobolev_forward_joint_smooth
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hF : ∀ m, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (F m (U (m + 2) t)) t)
    (hcoeff : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (U m t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × SingularClosure.Vec => smoothFourierSynthesis (U 0 z.1).val z.2)
      SingularClosure.forwardSpacetime :=
  SOBOLEV_CURVES_JOINT_SPACETIME_SMOOTH U
    (sobolev_forward_time_smooth U F htrace hF hderiv) hcoeff

/-- The synthesized field may be replaced by the pointwise equal actual physical field. -/
theorem actual_field_forward_joint_smooth
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (v : SingularClosure.Velocity)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hF : ∀ m, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (F m (U (m + 2) t)) t)
    (hcoeff : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (U m t).val = (U 0 t).val)
    (hphysical : ∀ (t : ℝ), 0 ≤ t →
      ∀ x, smoothFourierSynthesis (U 0 t).val x = v t x) :
    ContDiffOn ℝ ∞ (fun z : ℝ × SingularClosure.Vec => v z.1 z.2)
      SingularClosure.forwardSpacetime := by
  apply (sobolev_forward_joint_smooth U F htrace hF hderiv hcoeff).congr
  intro z hz
  exact (hphysical z.1 hz z.2).symm

end
end NSEGR.Strengthening
