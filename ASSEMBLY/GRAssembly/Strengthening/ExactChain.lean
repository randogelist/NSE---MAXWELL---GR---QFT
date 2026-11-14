import GRAssembly.Strengthening.PositiveProfiles
import GRAssembly.Strengthening.SourceUniqueness

/-!
Exact carrier assembly with three explicitly named analytic endpoints.
The endpoint propositions are not axioms and are not proofs of their own
inhabitation. The root below is conditional until their concrete bodies
are derived and externally audited. Every carrier is the literal source,
positive analytic profile, coherent NSE family, or native GR family.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Strengthening
noncomputable section

def PositiveTimeSmoothingEndpoint (ν : ℝ) (a : Field) : Prop :=
  ∀ s : NormalizedForwardTrajectory ν a,
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => s.totalVelocity z.1 z.2) positiveSpacetime ∧
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => s.totalPressure z.1 z.2) positiveSpacetime

def SmoothTrajectoryTraceEndpoint (ν : ℝ) (a : Field) : Prop :=
  ∀ s : NormalizedForwardTrajectory ν a,
    SpatialSmoothInitialTrace (fun t : PositiveTime => s.totalVelocity t.val) a

def PositiveProfileBoundaryEndpoint (ν : ℝ) (a : Field) : Prop :=
  ∀ r : PositiveProfileRepresentative ν a, ∃ (u : Velocity) (p : Pressure),
    NSEMaxwell.Classical.SmoothVelocity u ∧
    NSEMaxwell.Classical.SmoothPressure p ∧ u 0 = a ∧
    ∀ t : ℝ, 0 < t → u t = r.velocity t ∧ p t = r.pressure t

theorem spatialPeriodic_forward_of_positive
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → Vec → E)
    (hf : ContinuousOn (fun z : ℝ × Vec => f z.1 z.2)
      NSEMaxwell.Classical.forwardSpacetime)
    (hper : ∀ t : ℝ, 0 < t → SpatialPeriodic (f t)) :
    ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (f t) := by
  intro t ht x i
  have hshift : Continuous (fun z : ℝ × Vec => (z.1, z.2 + unitVector i)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  have hfshift : ContinuousOn (fun z : ℝ × Vec => f z.1 (z.2 + unitVector i))
      NSEMaxwell.Classical.forwardSpacetime :=
    hf.comp (s := NSEMaxwell.Classical.forwardSpacetime) hshift.continuousOn
      (fun _ hz => hz)
  have hz := continuousOn_forward_eq_zero_of_positive (hfshift.sub hf)
    (fun z hz => sub_eq_zero.mpr (hper z.1 hz z.2 i)) (t, x) ht
  exact sub_eq_zero.mp hz

theorem smoothProfileExtension_is_nssolution
    {ν : ℝ} {a : Field} (r : PositiveProfileRepresentative ν a)
    (u : Velocity) (p : Pressure)
    (hu : NSEMaxwell.Classical.SmoothVelocity u)
    (hp : NSEMaxwell.Classical.SmoothPressure p)
    (hi : u 0 = a)
    (he : ∀ t : ℝ, 0 < t → u t = r.velocity t ∧ p t = r.pressure t) :
    NSEMaxwell.Classical.NSSolution ν a u p := by
  apply nssolution_of_positive_time_equations hu hp
  · exact spatialPeriodic_forward_of_positive u hu.continuousOn (by
      intro t ht
      rw [(he t ht).1]
      exact r.solution.velocity_periodic t ht)
  · exact spatialPeriodic_forward_of_positive p hp.continuousOn (by
      intro t ht
      rw [(he t ht).2]
      exact r.solution.pressure_periodic t ht)
  · intro t ht x
    rw [(he t ht).1]
    exact r.solution.divergence_free t ht x
  · intro t ht x
    have hvel : u =ᶠ[𝓝 t] r.velocity := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (he s hs).1
    have hscalar : (fun s => u s x) =ᶠ[𝓝 t] (fun s => r.velocity s x) :=
      hvel.mono (fun _ hs => congrFun hs x)
    have hdt : localTimeDerivative u t x = localTimeDerivative r.velocity t x :=
      hscalar.deriv_eq
    simpa only [nseResidual, hdt, (he t ht).1, (he t ht).2] using
      r.solution.momentum t ht x
  · exact hi

def trajectoryToPositiveProfile {ν : ℝ} {a : Field}
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (s : NormalizedForwardTrajectory ν a) : PositiveTimeProfile ν a :=
  PositiveTimeProfile.mk {
    velocity := s.totalVelocity
    pressure := s.totalPressure
    solution := positiveAnalyticNSE_of_nssolution s.solution (hS s).1 (hS s).2
    origin_normalized := fun t => s.totalPressure_zero t.property.le
    spatial_trace := hT s }

theorem trajectoryToPositiveProfile_velocity {ν : ℝ} {a : Field}
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (s : NormalizedForwardTrajectory ν a) (t : PositiveTime) :
    (trajectoryToPositiveProfile hS hT s).velocity t = s.velocity t.val t.property.le :=
  s.totalVelocity_eq t.property.le

theorem trajectoryToPositiveProfile_pressure {ν : ℝ} {a : Field}
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (s : NormalizedForwardTrajectory ν a) (t : PositiveTime) :
    (trajectoryToPositiveProfile hS hT s).pressure t = s.pressure t.val t.property.le :=
  s.totalPressure_eq t.property.le

theorem trajectoryToPositiveProfile_injective {ν : ℝ} {a : Field}
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a) :
    Function.Injective (trajectoryToPositiveProfile hS hT) := by
  intro s r he
  apply NormalizedForwardTrajectory.eq_of_positive_velocity_eq s r
  intro t ht
  have hv := congrArg (fun p : PositiveTimeProfile ν a => p.velocity ⟨t, ht⟩) he
  simpa only [trajectoryToPositiveProfile_velocity] using hv

theorem trajectoryToPositiveProfile_surjective {ν : ℝ} {a : Field}
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    Function.Surjective (trajectoryToPositiveProfile hS hT) := by
  intro p
  refine Quotient.inductionOn p ?_
  intro r
  obtain ⟨u, q, hu, hq, hi, he⟩ := hE r
  have hsol := smoothProfileExtension_is_nssolution r u q hu hq hi he
  let s : NormalizedForwardTrajectory ν a := normalizedTrajectoryOfNSSolution hsol
  refine ⟨s, (PositiveTimeProfile.eq_iff_positive _ _).mpr ?_⟩
  intro t
  constructor
  · rw [trajectoryToPositiveProfile_velocity]
    change u t.val = r.velocity t.val
    exact (he t.val t.property).1
  · rw [trajectoryToPositiveProfile_pressure]
    change originNormalize q t.val = r.pressure t.val
    funext x
    change q t.val x - q t.val 0 = r.pressure t.val x
    rw [(he t.val t.property).2, r.origin_normalized t, sub_zero]

def trajectoryProfileEquiv {ν : ℝ} {a : Field}
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    NormalizedForwardTrajectory ν a ≃ PositiveTimeProfile ν a :=
  Equiv.ofBijective (trajectoryToPositiveProfile hS hT)
    ⟨trajectoryToPositiveProfile_injective hS hT,
      trajectoryToPositiveProfile_surjective hS hT hE⟩

def trajectoryGRFamilyEquiv {ν : ℝ} {a : Field}
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a :=
  (trajectoryProfileEquiv hS hT hE).trans (positiveProfileGRFamilyEquiv ν ρ hρ a)

theorem NSE_GR_POSITIVE_TIME_GERM_FAMILY_EQUIVALENCE_OF_ANALYTIC_ENDPOINTS
    (ν ρ : ℝ) (_hν : 0 < ν) (hρ : ρ ≠ 0)
    (a : Field) (_ha : NSEMaxwell.Classical.Data a)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    Nonempty (NormalizedForwardTrajectory ν a ≃ GRForwardFamily ν ρ a) :=
  ⟨trajectoryGRFamilyEquiv ρ hρ hS hT hE⟩

theorem nssolution_nonempty_gr_family_iff_of_analytic_endpoints
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field)
    (hS : PositiveTimeSmoothingEndpoint ν a)
    (hT : SmoothTrajectoryTraceEndpoint ν a)
    (hE : PositiveProfileBoundaryEndpoint ν a) :
    (∃ (u : Velocity) (p : Pressure), NSEMaxwell.Classical.NSSolution ν a u p) ↔
      Nonempty (GRForwardFamily ν ρ a) := by
  rw [literal_nssolution_nonempty_normalized_source]
  constructor
  · rintro ⟨s⟩
    exact ⟨trajectoryGRFamilyEquiv ρ hρ hS hT hE s⟩
  · rintro ⟨g⟩
    exact ⟨(trajectoryGRFamilyEquiv ρ hρ hS hT hE).symm g⟩

end
end NSEGR.Strengthening
