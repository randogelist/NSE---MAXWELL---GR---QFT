import GRAssembly.Strengthening.Calculus

/-!
The source carrier consists of normalized forward restrictions. Quotient
equality removes unconstrained negative-time values, while the native
`NSSolution` predicate and its within derivative at zero are preserved.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace NSEGR.Strengthening
noncomputable section

theorem nssolution_congr_forward {ν : ℝ} {a : Field}
    {u v : Velocity} {p q : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p)
    (hu : ∀ t : ℝ, 0 ≤ t → u t = v t)
    (hp : ∀ t : ℝ, 0 ≤ t → p t = q t) :
    NSEMaxwell.Classical.NSSolution ν a v q := by
  refine {
    velocity_smooth := ?_
    pressure_smooth := ?_
    velocity_periodic := ?_
    pressure_periodic := ?_
    divergence_free := ?_
    equation := ?_
    initial := ?_ }
  · have hs := h.velocity_smooth
    change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      NSEMaxwell.Classical.forwardSpacetime at hs
    exact hs.congr (fun z hz => congrFun (hu z.1 hz).symm z.2)
  · have hs := h.pressure_smooth
    change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      NSEMaxwell.Classical.forwardSpacetime at hs
    exact hs.congr (fun z hz => congrFun (hp z.1 hz).symm z.2)
  · intro t ht
    rw [← hu t ht]
    exact h.velocity_periodic t ht
  · intro t ht
    rw [← hp t ht]
    exact h.pressure_periodic t ht
  · intro t ht x
    rw [← hu t ht]
    exact h.divergence_free t ht x
  · intro t ht x
    have he := h.equation t ht x
    rw [NSEMaxwell.Classical.timeDerivative_congr hu ht x, hu t ht, hp t ht] at he
    exact he
  · exact (hu 0 le_rfl).symm.trans h.initial

structure NormalizedTrajectoryRepresentative (ν : ℝ) (a : Field) where
  velocity : Velocity
  pressure : Pressure
  solution : NSEMaxwell.Classical.NSSolution ν a velocity pressure
  origin_normalized : ∀ t : ℝ, 0 ≤ t → pressure t 0 = 0

def NormalizedTrajectoryRepresentative.setoid (ν : ℝ) (a : Field) :
    Setoid (NormalizedTrajectoryRepresentative ν a) where
  r s t := ∀ r : ℝ, 0 ≤ r → s.velocity r = t.velocity r ∧ s.pressure r = t.pressure r
  iseqv := {
    refl := fun _ _ _ => ⟨rfl, rfl⟩
    symm := by
      intro s t h r hr
      exact ⟨(h r hr).1.symm, (h r hr).2.symm⟩
    trans := by
      intro s t u hst htu r hr
      exact ⟨(hst r hr).1.trans (htu r hr).1, (hst r hr).2.trans (htu r hr).2⟩ }

abbrev NormalizedForwardTrajectory (ν : ℝ) (a : Field) :=
  Quotient (NormalizedTrajectoryRepresentative.setoid ν a)

def NormalizedForwardTrajectory.mk {ν : ℝ} {a : Field}
    (r : NormalizedTrajectoryRepresentative ν a) : NormalizedForwardTrajectory ν a :=
  Quotient.mk (NormalizedTrajectoryRepresentative.setoid ν a) r

theorem NormalizedForwardTrajectory.sound {ν : ℝ} {a : Field}
    {r s : NormalizedTrajectoryRepresentative ν a}
    (h : ∀ t : ℝ, 0 ≤ t → r.velocity t = s.velocity t ∧ r.pressure t = s.pressure t) :
    NormalizedForwardTrajectory.mk r = NormalizedForwardTrajectory.mk s :=
  Quotient.sound h

def NormalizedForwardTrajectory.velocity {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) (t : ℝ) (ht : 0 ≤ t) : Field :=
  Quotient.lift (fun r : NormalizedTrajectoryRepresentative ν a => r.velocity t)
    (by intro r s h; exact (h t ht).1) s

def NormalizedForwardTrajectory.pressure {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) (t : ℝ) (ht : 0 ≤ t) : ScalarField :=
  Quotient.lift (fun r : NormalizedTrajectoryRepresentative ν a => r.pressure t)
    (by intro r s h; exact (h t ht).2) s

@[simp] theorem NormalizedForwardTrajectory.velocity_mk {ν : ℝ} {a : Field}
    (r : NormalizedTrajectoryRepresentative ν a) (t : ℝ) (ht : 0 ≤ t) :
    (NormalizedForwardTrajectory.mk r).velocity t ht = r.velocity t := rfl

@[simp] theorem NormalizedForwardTrajectory.pressure_mk {ν : ℝ} {a : Field}
    (r : NormalizedTrajectoryRepresentative ν a) (t : ℝ) (ht : 0 ≤ t) :
    (NormalizedForwardTrajectory.mk r).pressure t ht = r.pressure t := rfl

theorem NormalizedForwardTrajectory.pressure_zero {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) (t : ℝ) (ht : 0 ≤ t) :
    s.pressure t ht 0 = 0 := by
  refine Quotient.inductionOn s ?_
  intro r
  exact r.origin_normalized t ht

theorem NormalizedForwardTrajectory.initial {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) : s.velocity 0 le_rfl = a := by
  refine Quotient.inductionOn s ?_
  intro r
  exact r.solution.initial

theorem NormalizedForwardTrajectory.eq_iff_forward {ν : ℝ} {a : Field}
    (s t : NormalizedForwardTrajectory ν a) :
    s = t ↔ ∀ r : ℝ, ∀ hr : 0 ≤ r,
      s.velocity r hr = t.velocity r hr ∧ s.pressure r hr = t.pressure r hr := by
  constructor
  · rintro rfl
    intro r hr
    exact ⟨rfl, rfl⟩
  · refine Quotient.inductionOn₂ s t ?_
    intro r q h
    exact Quotient.sound h

def NormalizedForwardTrajectory.totalVelocity {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) : Velocity :=
  fun t => if ht : 0 ≤ t then s.velocity t ht else fun _ => 0

def NormalizedForwardTrajectory.totalPressure {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) : Pressure :=
  fun t => if ht : 0 ≤ t then s.pressure t ht else fun _ => 0

theorem NormalizedForwardTrajectory.totalVelocity_eq {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) {t : ℝ} (ht : 0 ≤ t) :
    s.totalVelocity t = s.velocity t ht := by
  simp only [NormalizedForwardTrajectory.totalVelocity, dif_pos ht]

theorem NormalizedForwardTrajectory.totalPressure_eq {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) {t : ℝ} (ht : 0 ≤ t) :
    s.totalPressure t = s.pressure t ht := by
  simp only [NormalizedForwardTrajectory.totalPressure, dif_pos ht]

theorem NormalizedForwardTrajectory.solution {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) :
    NSEMaxwell.Classical.NSSolution ν a s.totalVelocity s.totalPressure := by
  refine Quotient.inductionOn s ?_
  intro r
  apply nssolution_congr_forward r.solution
  · intro t ht
    rw [NormalizedForwardTrajectory.totalVelocity_eq _ ht]
    rfl
  · intro t ht
    rw [NormalizedForwardTrajectory.totalPressure_eq _ ht]
    rfl

theorem NormalizedForwardTrajectory.totalPressure_zero {ν : ℝ} {a : Field}
    (s : NormalizedForwardTrajectory ν a) {t : ℝ} (ht : 0 ≤ t) :
    s.totalPressure t 0 = 0 := by
  rw [s.totalPressure_eq ht]
  exact s.pressure_zero t ht

def normalizedTrajectoryOfNSSolution {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) : NormalizedForwardTrajectory ν a :=
  NormalizedForwardTrajectory.mk {
    velocity := u
    pressure := originNormalize p
    solution := nssolution_originNormalize h
    origin_normalized := fun t _ => originNormalize_zero p t }

theorem literal_nssolution_nonempty_normalized_source (ν : ℝ) (a : Field) :
    (∃ (u : Velocity) (p : Pressure), NSEMaxwell.Classical.NSSolution ν a u p) ↔
      Nonempty (NormalizedForwardTrajectory ν a) := by
  constructor
  · rintro ⟨u, p, h⟩
    exact ⟨normalizedTrajectoryOfNSSolution h⟩
  · rintro ⟨s⟩
    exact ⟨s.totalVelocity, s.totalPressure, s.solution⟩

theorem feffermanB_iff_normalized_source_nonempty (ν : ℝ) :
    NSEMaxwell.Classical.FeffermanB ν ↔
      ∀ a : Field, NSEMaxwell.Classical.Data a → Nonempty (NormalizedForwardTrajectory ν a) := by
  constructor
  · intro h a ha
    exact (literal_nssolution_nonempty_normalized_source ν a).mp (h a ha)
  · intro h a ha
    exact (literal_nssolution_nonempty_normalized_source ν a).mpr (h a ha)

end
end NSEGR.Strengthening
