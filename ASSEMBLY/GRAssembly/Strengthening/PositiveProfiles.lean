import GRAssembly.Strengthening.SourceCarrier
import GRAssembly.Strengthening.GermFamilies
import GRAssembly.Strengthening.PositivePDE

/-!
Normalized analytic positive-time NSE profiles and coherent native NSE germs.
Profiles are quotiented by positive-time equality; nonpositive values carry
no additional data. Spatial initial traces are the actual Sobolev traces.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff

namespace NSEGR

noncomputable section

theorem sameFlowAt_center_origin_pressure {ν t0 : ℝ}
    {n m : NSERepresentative ν t0}
    (h : SameFlowAt t0 n.velocity n.pressure m.velocity m.pressure) :
    (fun x : Vec => n.pressure t0 x - n.pressure t0 0) =
      (fun x : Vec => m.pressure t0 x - m.pressure t0 0) := by
  have hp : (fun t x => n.pressure t x - n.pressure t 0) =ᶠ[𝓝 t0]
      (fun t x => m.pressure t x - m.pressure t 0) := by
    filter_upwards [h] with t ht
    obtain ⟨c, hc⟩ := ht.2
    funext x
    rw [hc x, hc 0]
    ring
  exact hp.eq_of_nhds

def NSEgerm.originPressureAtCenter {ν t0 : ℝ} : NSEgerm ν t0 → ScalarField :=
  Quotient.lift
    (fun n : NSERepresentative ν t0 => fun x : Vec => n.pressure t0 x - n.pressure t0 0)
    (fun _ _ h => sameFlowAt_center_origin_pressure h)

@[simp]
theorem NSEgerm.originPressureAtCenter_mk {ν t0 : ℝ}
    (n : NSERepresentative ν t0) :
    NSEgerm.originPressureAtCenter (NSEgerm.mk n) =
      (fun x : Vec => n.pressure t0 x - n.pressure t0 0) := rfl

theorem NSEgerm.originPressureAtCenter_zero {ν t0 : ℝ} (n : NSEgerm ν t0) :
    NSEgerm.originPressureAtCenter n 0 = 0 := by
  refine Quotient.inductionOn n ?_
  intro r
  simp

namespace Strengthening

structure PositiveProfileRepresentative (ν : ℝ) (a : Field) where
  velocity : Velocity
  pressure : Pressure
  solution : PositiveAnalyticNSE ν velocity pressure
  origin_normalized : ∀ t : PositiveTime, pressure t.val 0 = 0
  spatial_trace : SpatialSmoothInitialTrace (fun t : PositiveTime => velocity t.val) a

def PositiveProfileRepresentative.setoid (ν : ℝ) (a : Field) :
    Setoid (PositiveProfileRepresentative ν a) where
  r p q := ∀ t : PositiveTime,
    p.velocity t.val = q.velocity t.val ∧ p.pressure t.val = q.pressure t.val
  iseqv := {
    refl := fun _ _ => ⟨rfl, rfl⟩
    symm := by
      intro p q h t
      exact ⟨(h t).1.symm, (h t).2.symm⟩
    trans := by
      intro p q r hpq hqr t
      exact ⟨(hpq t).1.trans (hqr t).1, (hpq t).2.trans (hqr t).2⟩ }

abbrev PositiveTimeProfile (ν : ℝ) (a : Field) :=
  Quotient (PositiveProfileRepresentative.setoid ν a)

def PositiveTimeProfile.mk {ν : ℝ} {a : Field}
    (p : PositiveProfileRepresentative ν a) : PositiveTimeProfile ν a :=
  Quotient.mk (PositiveProfileRepresentative.setoid ν a) p

def PositiveTimeProfile.velocity {ν : ℝ} {a : Field}
    (p : PositiveTimeProfile ν a) (t : PositiveTime) : Field :=
  Quotient.lift
    (fun r : PositiveProfileRepresentative ν a => r.velocity t.val)
    (fun _ _ h => (h t).1) p

def PositiveTimeProfile.pressure {ν : ℝ} {a : Field}
    (p : PositiveTimeProfile ν a) (t : PositiveTime) : ScalarField :=
  Quotient.lift
    (fun r : PositiveProfileRepresentative ν a => r.pressure t.val)
    (fun _ _ h => (h t).2) p

@[simp]
theorem PositiveTimeProfile.velocity_mk {ν : ℝ} {a : Field}
    (p : PositiveProfileRepresentative ν a) (t : PositiveTime) :
    (PositiveTimeProfile.mk p).velocity t = p.velocity t.val := rfl

@[simp]
theorem PositiveTimeProfile.pressure_mk {ν : ℝ} {a : Field}
    (p : PositiveProfileRepresentative ν a) (t : PositiveTime) :
    (PositiveTimeProfile.mk p).pressure t = p.pressure t.val := rfl

theorem PositiveTimeProfile.pressure_zero {ν : ℝ} {a : Field}
    (p : PositiveTimeProfile ν a) (t : PositiveTime) : p.pressure t 0 = 0 := by
  refine Quotient.inductionOn p ?_
  intro r
  exact r.origin_normalized t

theorem PositiveTimeProfile.eq_iff_positive {ν : ℝ} {a : Field}
    (p q : PositiveTimeProfile ν a) :
    p = q ↔ ∀ t : PositiveTime, p.velocity t = q.velocity t ∧ p.pressure t = q.pressure t := by
  constructor
  · rintro rfl
    exact fun _ => ⟨rfl, rfl⟩
  · refine Quotient.inductionOn₂ p q ?_
    intro r s h
    exact Quotient.sound h

def positiveProfileRepresentativeToNSEFamily {ν : ℝ} {a : Field}
    (p : PositiveProfileRepresentative ν a) : NSEForwardFamily ν a := by
  let η : PositiveTimeNSEGermFamily ν := fun τ =>
    NSEgerm.mk (positiveTimeNSERepresentative p.solution τ.val τ.property)
  refine ⟨η, ?_, ?_⟩
  · intro τ
    refine ⟨positiveTimeNSERepresentative p.solution τ.val τ.property, rfl,
      τ.val / 2, half_pos τ.property, ?_, le_rfl, ?_⟩
    · linarith [τ.property]
    · intro t ht
      rfl
  · exact p.spatial_trace

theorem positiveProfileRepresentativeToNSEFamily_respects {ν : ℝ} {a : Field}
    (p q : PositiveProfileRepresentative ν a)
    (h : ∀ t : PositiveTime,
      p.velocity t.val = q.velocity t.val ∧ p.pressure t.val = q.pressure t.val) :
    positiveProfileRepresentativeToNSEFamily p = positiveProfileRepresentativeToNSEFamily q := by
  apply nseForwardFamily_ext
  intro τ
  apply NSEgerm.sound
  change SameFlowAt τ.val p.velocity p.pressure q.velocity q.pressure
  filter_upwards [Ioi_mem_nhds τ.property] with t ht
  refine ⟨(h ⟨t, ht⟩).1, 0, ?_⟩
  intro x
  rw [(h ⟨t, ht⟩).2]
  simp

def profileToNSEFamily {ν : ℝ} {a : Field} :
    PositiveTimeProfile ν a → NSEForwardFamily ν a :=
  Quotient.lift positiveProfileRepresentativeToNSEFamily
    (fun p q h => positiveProfileRepresentativeToNSEFamily_respects p q h)

@[simp]
theorem profileToNSEFamily_mk {ν : ℝ} {a : Field}
    (p : PositiveProfileRepresentative ν a) :
    profileToNSEFamily (PositiveTimeProfile.mk p) =
      positiveProfileRepresentativeToNSEFamily p := rfl

theorem profileToNSEFamily_velocity {ν : ℝ} {a : Field} (p : PositiveTimeProfile ν a) :
    nseFamilyVelocity (profileToNSEFamily p).val = p.velocity := by
  refine Quotient.inductionOn p ?_
  intro r
  rfl

theorem profileToNSEFamily_pressure {ν : ℝ} {a : Field}
    (p : PositiveTimeProfile ν a) (t : PositiveTime) :
    NSEgerm.originPressureAtCenter ((profileToNSEFamily p).val t) = p.pressure t := by
  refine Quotient.inductionOn p ?_
  intro r
  funext x
  change r.pressure t.val x - r.pressure t.val 0 = r.pressure t.val x
  rw [r.origin_normalized t]
  simp

theorem profileToNSEFamily_injective {ν : ℝ} {a : Field} :
    Function.Injective (profileToNSEFamily (ν := ν) (a := a)) := by
  intro p q hpq
  apply (PositiveTimeProfile.eq_iff_positive p q).mpr
  intro t
  constructor
  · calc
      p.velocity t = nseFamilyVelocity (profileToNSEFamily p).val t :=
        (congrFun (profileToNSEFamily_velocity p) t).symm
      _ = nseFamilyVelocity (profileToNSEFamily q).val t :=
        congrArg (fun η : NSEForwardFamily ν a => nseFamilyVelocity η.val t) hpq
      _ = q.velocity t := congrFun (profileToNSEFamily_velocity q) t
  · calc
      p.pressure t = NSEgerm.originPressureAtCenter ((profileToNSEFamily p).val t) :=
        (profileToNSEFamily_pressure p t).symm
      _ = NSEgerm.originPressureAtCenter ((profileToNSEFamily q).val t) :=
        congrArg (fun η : NSEForwardFamily ν a => NSEgerm.originPressureAtCenter (η.val t)) hpq
      _ = q.pressure t := profileToNSEFamily_pressure q t

def nseFamilyPressure {ν : ℝ} (η : PositiveTimeNSEGermFamily ν) :
    PositiveTime → ScalarField :=
  fun t => NSEgerm.originPressureAtCenter (η t)

def positiveVelocityTotal (V : PositiveTime → Field) : Velocity :=
  fun t => if ht : 0 < t then V ⟨t, ht⟩ else fun _ => 0

def positivePressureTotal (Q : PositiveTime → ScalarField) : Pressure :=
  fun t => if ht : 0 < t then Q ⟨t, ht⟩ else fun _ => 0

@[simp]
theorem positiveVelocityTotal_at (V : PositiveTime → Field) (t : PositiveTime) :
    positiveVelocityTotal V t.val = V t := by
  simp only [positiveVelocityTotal, dif_pos t.property]

@[simp]
theorem positivePressureTotal_at (Q : PositiveTime → ScalarField) (t : PositiveTime) :
    positivePressureTotal Q t.val = Q t := by
  simp only [positivePressureTotal, dif_pos t.property]

theorem coherent_nse_family_pressure_match {ν : ℝ}
    (η : PositiveTimeNSEGermFamily ν) (hη : NSEVelocityCoherent η)
    (τ : PositiveTime) (n : NSERepresentative ν τ.val) (d : ℝ)
    (hdn : d ≤ n.radius)
    (hcoh : ∀ s : PositiveTime, s.val ∈ timeInterval τ.val d →
      n.velocity s.val = nseFamilyVelocity η s)
    (t : PositiveTime) (ht : t.val ∈ timeInterval τ.val d) :
    originNormalize n.pressure t.val = nseFamilyPressure η t := by
  obtain ⟨m, hm, e, he, _, hem, hmcoh⟩ := hη t
  have htOld : timeInterval τ.val d ∈ 𝓝 t.val :=
    isOpen_Ioo.mem_nhds ht
  have htNew : timeInterval t.val e ∈ 𝓝 t.val := timeInterval_mem_nhds t.val e he
  have hvel : n.velocity =ᶠ[𝓝 t.val] m.velocity := by
    filter_upwards [htOld, htNew, Ioi_mem_nhds t.property] with s hsOld hsNew hsPos
    exact (hcoh ⟨s, hsPos⟩ hsOld).trans (hmcoh ⟨s, hsPos⟩ hsNew).symm
  have htCenter : t.val ∈ timeInterval t.val e := by
    change t.val - e < t.val ∧ t.val < t.val + e
    constructor <;> linarith
  have hp := localNSE_originNormalize_eq_of_eventuallyEq n.solution m.solution
    (timeInterval_mono hdn ht) (timeInterval_mono hem htCenter) hvel
  calc
    originNormalize n.pressure t.val = originNormalize m.pressure t.val := hp
    _ = nseFamilyPressure η t := by
      change NSEgerm.originPressureAtCenter (NSEgerm.mk m) =
        NSEgerm.originPressureAtCenter (η t)
      rw [hm]

/-- Local equality with actual analytic NSE representatives transfers every
analytic, periodic and PDE field of the positive-time profile predicate. -/
theorem positiveAnalyticNSE_of_local_representatives {ν : ℝ}
    (u : Velocity) (p : Pressure)
    (hlocal : ∀ τ : PositiveTime, ∃ n : NSERepresentative ν τ.val,
      ∃ d : ℝ, 0 < d ∧ d < τ.val ∧ d ≤ n.radius ∧
        ∀ t ∈ timeInterval τ.val d, u t = n.velocity t ∧ p t = n.pressure t) :
    PositiveAnalyticNSE ν u p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, d, hd, _, hdn, heq⟩ := hlocal ⟨z.1, hz⟩
    have hcenter : z.1 ∈ timeInterval z.1 d := by
      change z.1 - d < z.1 ∧ z.1 < z.1 + d
      constructor <;> linarith
    have hI : timeInterval z.1 d ∈ 𝓝 z.1 := timeInterval_mem_nhds z.1 d hd
    have hzI : ∀ᶠ w : ℝ × Vec in 𝓝 z, w.1 ∈ timeInterval z.1 d :=
      continuous_fst.continuousAt.tendsto.eventually hI
    apply (n.solution.velocity_analytic z (timeInterval_mono hdn hcenter)).congr
    filter_upwards [hzI] with w hw
    exact congrFun (heq w.1 hw).1.symm w.2
  · intro z hz
    obtain ⟨n, d, hd, _, hdn, heq⟩ := hlocal ⟨z.1, hz⟩
    have hcenter : z.1 ∈ timeInterval z.1 d := by
      change z.1 - d < z.1 ∧ z.1 < z.1 + d
      constructor <;> linarith
    have hI : timeInterval z.1 d ∈ 𝓝 z.1 := timeInterval_mem_nhds z.1 d hd
    have hzI : ∀ᶠ w : ℝ × Vec in 𝓝 z, w.1 ∈ timeInterval z.1 d :=
      continuous_fst.continuousAt.tendsto.eventually hI
    apply (n.solution.pressure_analytic z (timeInterval_mono hdn hcenter)).congr
    filter_upwards [hzI] with w hw
    exact congrFun (heq w.1 hw).2.symm w.2
  · intro t ht
    obtain ⟨n, d, hd, _, hdn, heq⟩ := hlocal ⟨t, ht⟩
    have hcenter : t ∈ timeInterval t d := by
      change t - d < t ∧ t < t + d
      constructor <;> linarith
    rw [(heq t hcenter).1]
    exact n.solution.periodic_velocity t (timeInterval_mono hdn hcenter)
  · intro t ht
    obtain ⟨n, d, hd, _, hdn, heq⟩ := hlocal ⟨t, ht⟩
    have hcenter : t ∈ timeInterval t d := by
      change t - d < t ∧ t < t + d
      constructor <;> linarith
    rw [(heq t hcenter).2]
    exact n.solution.periodic_pressure t (timeInterval_mono hdn hcenter)
  · intro t ht x
    obtain ⟨n, d, hd, _, hdn, heq⟩ := hlocal ⟨t, ht⟩
    have hcenter : t ∈ timeInterval t d := by
      change t - d < t ∧ t < t + d
      constructor <;> linarith
    rw [(heq t hcenter).1]
    exact n.solution.divergence_free t (timeInterval_mono hdn hcenter) x
  · intro t ht x
    obtain ⟨n, d, hd, _, hdn, heq⟩ := hlocal ⟨t, ht⟩
    have hcenter : t ∈ timeInterval t d := by
      change t - d < t ∧ t < t + d
      constructor <;> linarith
    have hI : timeInterval t d ∈ 𝓝 t := timeInterval_mem_nhds t d hd
    have htime : (fun s => u s x) =ᶠ[𝓝 t] (fun s => n.velocity s x) := by
      filter_upwards [hI] with s hs
      exact congrFun (heq s hs).1 x
    rw [nseResidual, localTimeDerivative, htime.deriv_eq,
      (heq t hcenter).1, (heq t hcenter).2]
    exact n.solution.momentum t (timeInterval_mono hdn hcenter) x

theorem coherent_nse_family_positiveAnalyticNSE {ν : ℝ}
    (η : PositiveTimeNSEGermFamily ν) (hη : NSEVelocityCoherent η) :
    PositiveAnalyticNSE ν (positiveVelocityTotal (nseFamilyVelocity η))
      (positivePressureTotal (nseFamilyPressure η)) := by
  apply positiveAnalyticNSE_of_local_representatives
  intro τ
  obtain ⟨n, hn, d, hd, hdτ, hdn, hcoh⟩ := hη τ
  let normalized : NSERepresentative ν τ.val := {
    radius := n.radius
    velocity := n.velocity
    pressure := originNormalize n.pressure
    solution := localNSE_originNormalize n.solution }
  refine ⟨normalized, d, hd, hdτ, hdn, ?_⟩
  intro t ht
  have htPos : 0 < t := by
    have htLeft : τ.val - d < t := ht.1
    linarith
  constructor
  · change positiveVelocityTotal (nseFamilyVelocity η) t = n.velocity t
    rw [show positiveVelocityTotal (nseFamilyVelocity η) t =
      nseFamilyVelocity η ⟨t, htPos⟩ from positiveVelocityTotal_at _ ⟨t, htPos⟩]
    exact (hcoh ⟨t, htPos⟩ ht).symm
  · change positivePressureTotal (nseFamilyPressure η) t = originNormalize n.pressure t
    rw [show positivePressureTotal (nseFamilyPressure η) t =
      nseFamilyPressure η ⟨t, htPos⟩ from positivePressureTotal_at _ ⟨t, htPos⟩]
    exact (coherent_nse_family_pressure_match η hη τ n d hdn hcoh ⟨t, htPos⟩ ht).symm

def nseFamilyToProfileRepresentative {ν : ℝ} {a : Field}
    (η : NSEForwardFamily ν a) : PositiveProfileRepresentative ν a where
  velocity := positiveVelocityTotal (nseFamilyVelocity η.val)
  pressure := positivePressureTotal (nseFamilyPressure η.val)
  solution := coherent_nse_family_positiveAnalyticNSE η.val η.property.1
  origin_normalized := by
    intro t
    rw [positivePressureTotal_at]
    exact NSEgerm.originPressureAtCenter_zero (η.val t)
  spatial_trace := by
    have heq : (fun t : PositiveTime => positiveVelocityTotal (nseFamilyVelocity η.val) t.val) =
        nseFamilyVelocity η.val := by
      funext t
      exact positiveVelocityTotal_at _ t
    rw [heq]
    exact η.property.2

def nseFamilyToProfile {ν : ℝ} {a : Field}
    (η : NSEForwardFamily ν a) : PositiveTimeProfile ν a :=
  PositiveTimeProfile.mk (nseFamilyToProfileRepresentative η)

theorem profileToNSEFamily_nseFamilyToProfile {ν : ℝ} {a : Field}
    (η : NSEForwardFamily ν a) :
    profileToNSEFamily (nseFamilyToProfile η) = η := by
  apply nseForwardFamily_ext
  intro τ
  obtain ⟨n, hn, d, hd, hdτ, hdn, hcoh⟩ := η.property.1 τ
  apply Eq.trans _ hn
  apply NSEgerm.sound
  change SameFlowAt τ.val (positiveVelocityTotal (nseFamilyVelocity η.val))
    (positivePressureTotal (nseFamilyPressure η.val)) n.velocity n.pressure
  have hI : timeInterval τ.val d ∈ 𝓝 τ.val := timeInterval_mem_nhds τ.val d hd
  filter_upwards [hI, Ioi_mem_nhds τ.property] with t ht htPos
  refine ⟨?_, -n.pressure t 0, ?_⟩
  · rw [show positiveVelocityTotal (nseFamilyVelocity η.val) t =
      nseFamilyVelocity η.val ⟨t, htPos⟩ from positiveVelocityTotal_at _ ⟨t, htPos⟩]
    exact (hcoh ⟨t, htPos⟩ ht).symm
  · intro x
    have hp := coherent_nse_family_pressure_match η.val η.property.1 τ n d hdn hcoh
      ⟨t, htPos⟩ ht
    have htotal := positivePressureTotal_at (nseFamilyPressure η.val) ⟨t, htPos⟩
    rw [htotal, ← hp]
    simp only [originNormalize, sub_eq_add_neg]

theorem nseFamilyToProfile_profileToNSEFamily {ν : ℝ} {a : Field}
    (p : PositiveTimeProfile ν a) :
    nseFamilyToProfile (profileToNSEFamily p) = p :=
  profileToNSEFamily_injective (profileToNSEFamily_nseFamilyToProfile (profileToNSEFamily p))

def profileNSEFamilyEquiv (ν : ℝ) (a : Field) :
    PositiveTimeProfile ν a ≃ NSEForwardFamily ν a where
  toFun := profileToNSEFamily
  invFun := nseFamilyToProfile
  left_inv := nseFamilyToProfile_profileToNSEFamily
  right_inv := profileToNSEFamily_nseFamilyToProfile

theorem POSITIVE_PROFILE_NSE_FAMILY_EQUIVALENCE (ν : ℝ) (a : Field) :
    Nonempty (PositiveTimeProfile ν a ≃ NSEForwardFamily ν a) :=
  ⟨profileNSEFamilyEquiv ν a⟩

def positiveProfileGRFamilyEquiv (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field) :
    PositiveTimeProfile ν a ≃ GRForwardFamily ν ρ a :=
  (profileNSEFamilyEquiv ν a).trans (coherentFamilyEquiv ν ρ hρ a)

theorem POSITIVE_PROFILE_GR_FAMILY_EQUIVALENCE (ν ρ : ℝ)
    (_hν : 0 < ν) (hρ : ρ ≠ 0) (a : Field) :
    Nonempty (PositiveTimeProfile ν a ≃ GRForwardFamily ν ρ a) :=
  ⟨positiveProfileGRFamilyEquiv ν ρ hρ a⟩

end Strengthening
end
end NSEGR
