import GRAssembly.Strengthening.SobolevTrace
import SingularClosure.SobolevPressure

/-!
# Literal Fourier NSE boundary and normalized-pressure composition

The generic boundary construction is instantiated with the actual continuous
quadratic Fourier NSE right hand side. Pressure is constructed from the actual
untruncated transport and normalized by evaluation at the spatial origin.

The hypothesis `hderiv` is the exact positive-time Sobolev norm derivative.
Its derivation from the physical trajectory is G30 and remains separate.
Neither coefficientwise differentiation nor a supplied derivative certificate
is identified here with discharge of that physical obligation.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff
open SingularClosure

namespace NSEGR.Strengthening
noncomputable section

/-- The actual nonlinear Fourier equation has a right derivative at zero. -/
theorem fourierNSE_right_boundary_equation
    (ν : ℝ) (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (fourierSobolevRhs ν m (U (m + 2) t)) t)
    (m : ℕ) :
    HasDerivWithinAt (U m) (fourierSobolevRhs ν m (U (m + 2) 0))
      (Ici (0 : ℝ)) 0 :=
  sobolev_right_boundary_equation U (fourierSobolevRhs ν) htrace
    (fun m => (fourierSobolevRhs_contDiff ν m).continuous) hderiv m

/-- Every actual Sobolev curve is smooth through the initial time. -/
theorem fourierNSE_forward_time_smooth
    (ν : ℝ) (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (fourierSobolevRhs ν m (U (m + 2) t)) t) :
    ∀ m, ContDiffOn ℝ ∞ (U m) (Ici (0 : ℝ)) :=
  sobolev_forward_time_smooth U (fourierSobolevRhs ν) htrace
    (fourierSobolevRhs_contDiff ν) hderiv

/-- Actual Fourier synthesis is jointly smooth on the closed forward domain. -/
theorem fourierNSE_forward_joint_smooth
    (ν : ℝ) (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (fourierSobolevRhs ν m (U (m + 2) t)) t)
    (hcoeff : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (U m t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × SingularClosure.Vec => smoothFourierSynthesis (U 0 z.1).val z.2)
      SingularClosure.forwardSpacetime :=
  sobolev_forward_joint_smooth U (fourierSobolevRhs ν) htrace
    (fourierSobolevRhs_contDiff ν) hderiv hcoeff

/-- The pressure is the literal transport multiplier with its origin value removed. -/
def normalizedSobolevPressure (U : ∀ m : ℕ, ℝ → TorusSobolev m) :
    SingularClosure.Pressure :=
  fun t x => fullTransportPressure (U 0 t) x - fullTransportPressure (U 0 t) 0

@[simp]
theorem normalizedSobolevPressure_origin
    (U : ∀ m : ℕ, ℝ → TorusSobolev m) (t : ℝ) :
    normalizedSobolevPressure U t 0 = 0 := by
  simp only [normalizedSobolevPressure, sub_self]

theorem normalizedSobolevPressure_periodic
    (U : ∀ m : ℕ, ℝ → TorusSobolev m) (t : ℝ) :
    SingularClosure.SpatialPeriodic (normalizedSobolevPressure U t) := by
  intro x i
  unfold normalizedSobolevPressure
  rw [fullTransportPressure_periodic (U 0 t) x i]

/-- No independent pressure trace is required by the actual quadratic pressure map. -/
theorem normalizedSobolevPressure_joint_smooth
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (hU : ∀ m, ContDiffOn ℝ ∞ (U m) (Ici (0 : ℝ)))
    (hcoeff : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (U m t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × SingularClosure.Vec => normalizedSobolevPressure U z.1 z.2)
      SingularClosure.forwardSpacetime := by
  have hp := SOBOLEV_TRANSPORT_PRESSURE_JOINT_SMOOTH U hU hcoeff
  have hz : ContDiffOn ℝ ∞
      (fun z : ℝ × SingularClosure.Vec => (z.1, (0 : SingularClosure.Vec)))
      SingularClosure.forwardSpacetime :=
    (contDiff_fst.prodMk contDiff_const).contDiffOn
  have hp0 : ContDiffOn ℝ ∞
      (fun z : ℝ × SingularClosure.Vec => fullTransportPressure (U 0 z.1) 0)
      SingularClosure.forwardSpacetime :=
    hp.comp hz (fun z h => h)
  exact hp.sub hp0

/-- The normalized physical pressure inherits joint smoothness from the velocity trace. -/
theorem fourierNSE_normalized_pressure_joint_smooth
    (ν : ℝ) (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (fourierSobolevRhs ν m (U (m + 2) t)) t)
    (hcoeff : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (U m t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × SingularClosure.Vec => normalizedSobolevPressure U z.1 z.2)
      SingularClosure.forwardSpacetime :=
  normalizedSobolevPressure_joint_smooth U
    (fourierNSE_forward_time_smooth ν U htrace hderiv) hcoeff

/-- Pointwise physical Fourier identification transfers both actual smooth fields. -/
theorem actual_NSE_fields_forward_joint_smooth
    (ν : ℝ) (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (v : SingularClosure.Velocity) (q : SingularClosure.Pressure)
    (htrace : ∀ m, Tendsto (U m) (𝓝[>] (0 : ℝ)) (𝓝 (U m 0)))
    (hderiv : ∀ (m : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (U m) (fourierSobolevRhs ν m (U (m + 2) t)) t)
    (hcoeff : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (U m t).val = (U 0 t).val)
    (hv : ∀ t, 0 ≤ t → ∀ x, smoothFourierSynthesis (U 0 t).val x = v t x)
    (hq : ∀ t, 0 ≤ t → ∀ x, normalizedSobolevPressure U t x = q t x) :
    ContDiffOn ℝ ∞ (fun z : ℝ × SingularClosure.Vec => v z.1 z.2)
        SingularClosure.forwardSpacetime ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × SingularClosure.Vec => q z.1 z.2)
        SingularClosure.forwardSpacetime := by
  refine ⟨actual_field_forward_joint_smooth U (fourierSobolevRhs ν) v htrace
    (fourierSobolevRhs_contDiff ν) hderiv hcoeff hv, ?_⟩
  apply (fourierNSE_normalized_pressure_joint_smooth ν U htrace hderiv hcoeff).congr
  intro z hz
  exact (hq z.1 hz z.2).symm

end
end NSEGR.Strengthening
