import GRAssembly.Strengthening.SmoothingEndpoint
import GRAssembly.Strengthening.BoundaryIdentities
import GRAssembly.Strengthening.PositiveProfiles
import GRAssembly.Strengthening.SourceUniqueness

/-!
Relation-first source carrier.

The positive-time analyticity witness is carried by each source element.
No universal smoothing premise is required by the carrier or by the
analytic-source/GR correspondence.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Strengthening
noncomputable section

structure AnalyticForwardTrajectory (ν : ℝ) (a : Field) where
  trajectory : NormalizedForwardTrajectory ν a
  velocity_analytic :
    AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => trajectory.totalVelocity z.1 z.2)
      positiveSpacetime

@[ext]
theorem AnalyticForwardTrajectory.ext {ν : ℝ} {a : Field}
    {s r : AnalyticForwardTrajectory ν a}
    (h : s.trajectory = r.trajectory) : s = r := by
  cases s
  cases r
  cases h
  rfl

theorem AnalyticForwardTrajectory.pressure_analytic
    {ν : ℝ} {a : Field} (s : AnalyticForwardTrajectory ν a) :
    AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => s.trajectory.totalPressure z.1 z.2)
      positiveSpacetime := by
  have h := nssolution_originNormalize_positive_analytic
    s.trajectory.solution s.velocity_analytic
  simpa only [s.trajectory.originNormalize_totalPressure] using h

def AnalyticForwardTrajectory.positiveNSE
    {ν : ℝ} {a : Field} (s : AnalyticForwardTrajectory ν a) :
    PositiveAnalyticNSE ν s.trajectory.totalVelocity s.trajectory.totalPressure :=
  positiveAnalyticNSE_of_nssolution s.trajectory.solution
    s.velocity_analytic s.pressure_analytic

def analyticForwardToPositiveProfile
    {ν : ℝ} {a : Field} (s : AnalyticForwardTrajectory ν a) :
    PositiveTimeProfile ν a :=
  PositiveTimeProfile.mk {
    velocity := s.trajectory.totalVelocity
    pressure := s.trajectory.totalPressure
    solution := s.positiveNSE
    origin_normalized := fun t => s.trajectory.totalPressure_zero t.property.le
    spatial_trace := smoothTrajectoryTraceEndpoint ν a s.trajectory }

@[simp]
theorem analyticForwardToPositiveProfile_velocity
    {ν : ℝ} {a : Field} (s : AnalyticForwardTrajectory ν a)
    (t : PositiveTime) :
    (analyticForwardToPositiveProfile s).velocity t =
      s.trajectory.velocity t.val t.property.le := by
  change s.trajectory.totalVelocity t.val =
    s.trajectory.velocity t.val t.property.le
  exact s.trajectory.totalVelocity_eq t.property.le

@[simp]
theorem analyticForwardToPositiveProfile_pressure
    {ν : ℝ} {a : Field} (s : AnalyticForwardTrajectory ν a)
    (t : PositiveTime) :
    (analyticForwardToPositiveProfile s).pressure t =
      s.trajectory.pressure t.val t.property.le := by
  change s.trajectory.totalPressure t.val =
    s.trajectory.pressure t.val t.property.le
  exact s.trajectory.totalPressure_eq t.property.le

theorem analyticForwardToPositiveProfile_injective
    {ν : ℝ} {a : Field} :
    Function.Injective
      (analyticForwardToPositiveProfile :
        AnalyticForwardTrajectory ν a → PositiveTimeProfile ν a) := by
  intro s r h
  apply AnalyticForwardTrajectory.ext
  apply NormalizedForwardTrajectory.eq_of_positive_velocity_eq
  intro t ht
  have hv := congrArg
    (fun p : PositiveTimeProfile ν a => p.velocity ⟨t, ht⟩) h
  simpa only [analyticForwardToPositiveProfile_velocity] using hv

def profileRepresentativeToAnalyticForward
    {ν : ℝ} {a : Field} (ha : NSEMaxwell.Classical.Data a)
    (r : PositiveProfileRepresentative ν a) :
    AnalyticForwardTrajectory ν a := by
  let hsol := profileBoundary_is_nssolution ha r
  let s : NormalizedForwardTrajectory ν a :=
    normalizedTrajectoryOfNSSolution hsol
  refine ⟨s, ?_⟩
  intro z hz
  apply (r.solution.velocity_analytic z hz).congr
  filter_upwards [Ioi_mem_nhds hz] with w hw
  change r.velocity w.1 w.2 = s.totalVelocity w.1 w.2
  rw [s.totalVelocity_eq hw.le]
  change r.velocity w.1 w.2 = profileBoundaryVelocity r w.1 w.2
  exact congrFun (profileBoundaryVelocity_positive r hw).symm w.2

theorem analyticForwardToPositiveProfile_profileRepresentativeToAnalyticForward
    {ν : ℝ} {a : Field} (ha : NSEMaxwell.Classical.Data a)
    (r : PositiveProfileRepresentative ν a) :
    analyticForwardToPositiveProfile
        (profileRepresentativeToAnalyticForward ha r) =
      PositiveTimeProfile.mk r := by
  apply (PositiveTimeProfile.eq_iff_positive _ _).mpr
  intro t
  constructor
  · rw [analyticForwardToPositiveProfile_velocity]
    change profileBoundaryVelocity r t.val = r.velocity t.val
    exact profileBoundaryVelocity_positive r t.property
  · rw [analyticForwardToPositiveProfile_pressure]
    change originNormalize (profileBoundaryPressure r) t.val = r.pressure t.val
    funext x
    change profileBoundaryPressure r t.val x -
      profileBoundaryPressure r t.val 0 = r.pressure t.val x
    rw [profileBoundaryPressure_positive r t.property, r.origin_normalized t]
    simp

theorem analyticForwardToPositiveProfile_surjective
    {ν : ℝ} {a : Field} (ha : NSEMaxwell.Classical.Data a) :
    Function.Surjective
      (analyticForwardToPositiveProfile :
        AnalyticForwardTrajectory ν a → PositiveTimeProfile ν a) := by
  intro p
  refine Quotient.inductionOn p ?_
  intro r
  exact ⟨profileRepresentativeToAnalyticForward ha r,
    analyticForwardToPositiveProfile_profileRepresentativeToAnalyticForward ha r⟩

noncomputable def analyticForwardProfileEquiv
    (ν : ℝ) (a : Field) (ha : NSEMaxwell.Classical.Data a) :
    AnalyticForwardTrajectory ν a ≃ PositiveTimeProfile ν a :=
  Equiv.ofBijective
    (analyticForwardToPositiveProfile :
      AnalyticForwardTrajectory ν a → PositiveTimeProfile ν a)
    ⟨analyticForwardToPositiveProfile_injective,
      analyticForwardToPositiveProfile_surjective ha⟩

@[simp]
theorem analyticForwardProfileEquiv_apply
    (ν : ℝ) (a : Field) (ha : NSEMaxwell.Classical.Data a)
    (s : AnalyticForwardTrajectory ν a) :
    analyticForwardProfileEquiv ν a ha s =
      analyticForwardToPositiveProfile s := rfl

end
end NSEGR.Strengthening
