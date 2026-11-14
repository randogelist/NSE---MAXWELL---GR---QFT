import GRAssembly.Strengthening.ExactChain
import GRAssembly.Strengthening.PressureIdentification

/-! Actual encoding, decoding and normalized-pressure formulas for the exact chain. -/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

theorem trajectoryGRFamilyEquiv_apply_germ {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (s : NormalizedForwardTrajectory ν a) (τ : PositiveTime) :
    (trajectoryGRFamilyEquiv ρ hρ hS hT hE s).val τ =
      nativeLocalEquiv ν ρ τ.val hρ
        (NSEgerm.mk (positiveTimeNSERepresentative
          (positiveAnalyticNSE_of_nssolution s.solution (hS s).1 (hS s).2)
          τ.val τ.property)) := rfl

theorem trajectoryGRFamilyEquiv_velocity {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (s : NormalizedForwardTrajectory ν a) (t : PositiveTime) :
    grFamilyVelocity (trajectoryGRFamilyEquiv ρ hρ hS hT hE s).val t =
      s.velocity t.val t.property.le := by
  change grFamilyVelocity
    (coherentFamilyEquiv ν ρ hρ a
      (profileToNSEFamily (trajectoryToPositiveProfile hS hT s))).val t = _
  rw [coherentFamilyEquiv_velocity, profileToNSEFamily_velocity,
    trajectoryToPositiveProfile_velocity]

theorem trajectoryGRFamilyEquiv_inverse_velocity {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (g : GRForwardFamily ν ρ a) (t : PositiveTime) :
    ((trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g).velocity t.val t.property.le =
      grFamilyVelocity g.val t := by
  have h := trajectoryGRFamilyEquiv_velocity ρ hρ hS hT hE
    ((trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g) t
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem normalizedForwardTrajectory_pressure_eq_quadratic
    {ν : ℝ} {a : Field} (s : NormalizedForwardTrajectory ν a)
    {t : ℝ} (ht : 0 ≤ t) :
    s.pressure t ht = normalizedQuadraticPressure (s.velocity t ht) := by
  have h := nssolution_normalized_pressure_eq_quadraticPoisson s.solution ht
  simpa only [originNormalize, s.totalPressure_zero ht, sub_zero,
    s.totalPressure_eq ht, s.totalVelocity_eq ht] using h

theorem trajectoryGRFamilyEquiv_inverse_pressure {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (g : GRForwardFamily ν ρ a) (t : PositiveTime) :
    ((trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g).pressure t.val t.property.le =
      normalizedQuadraticPressure (grFamilyVelocity g.val t) := by
  rw [normalizedForwardTrajectory_pressure_eq_quadratic,
    trajectoryGRFamilyEquiv_inverse_velocity]

theorem trajectoryGRFamilyEquiv_inverse_initial {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (g : GRForwardFamily ν ρ a) :
    ((trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g).velocity 0 le_rfl = a ∧
    ((trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g).pressure 0 le_rfl =
      normalizedQuadraticPressure a := by
  constructor
  · exact NormalizedForwardTrajectory.initial _
  · rw [normalizedForwardTrajectory_pressure_eq_quadratic,
      NormalizedForwardTrajectory.initial]

theorem trajectoryGRFamilyEquiv_left_inverse {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (s : NormalizedForwardTrajectory ν a) :
    (trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm
      (trajectoryGRFamilyEquiv ρ hρ hS hT hE s) = s :=
  Equiv.symm_apply_apply _ s

theorem trajectoryGRFamilyEquiv_right_inverse {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a)
    (g : GRForwardFamily ν ρ a) :
    trajectoryGRFamilyEquiv ρ hρ hS hT hE
      ((trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g) = g :=
  Equiv.apply_symm_apply _ g

end
end NSEGR.Strengthening
