import GRAdapter.Germs
import NSEMaxwell.Kinematics

/-!
Exact positive-time calculus, smooth pressure normalization and analytic
representatives for the frozen GR strengthening. No analytic smoothing or
global solution existence is postulated by these interface theorems.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff Topology

namespace NSEGR.Strengthening
noncomputable section

theorem spatialPartial_eq_coordinateDerivative (v : Field) (i : Fin 3) (x : Vec) :
    NSEGR.spatialPartial v i x = NSEMaxwell.Classical.coordinateDerivative v i x := rfl

theorem gradient_eq_classical (p : ScalarField) :
    NSEGR.gradient p = NSEMaxwell.Classical.gradient p := rfl

theorem divergence_eq_classical (v : Field) :
    NSEGR.divergence v = NSEMaxwell.Classical.divergence v := rfl

theorem laplacian_eq_classical (v : Field) :
    NSEGR.laplacian v = NSEMaxwell.Classical.laplacian v := rfl

theorem convection_eq_classical (v : Field) :
    NSEGR.convection v = NSEMaxwell.Classical.convection v := rfl

theorem spatialPeriodic_iff_classical {E : Type*} (f : Vec → E) :
    NSEGR.SpatialPeriodic f ↔ NSEMaxwell.Classical.SpatialPeriodic f := Iff.rfl

theorem timeDerivative_eq_localTimeDerivative (u : Velocity) {t : ℝ}
    (ht : 0 < t) (x : Vec) :
    NSEMaxwell.Classical.timeDerivative u t x = NSEGR.localTimeDerivative u t x := by
  exact derivWithin_of_mem_nhds (Ici_mem_nhds ht)

theorem scalarTimeDerivative_eq_localTimeDerivative (p : Pressure) {t : ℝ}
    (ht : 0 < t) (x : Vec) :
    NSEMaxwell.Classical.scalarTimeDerivative p t x =
      NSEGR.scalarLocalTimeDerivative p t x := by
  exact derivWithin_of_mem_nhds (Ici_mem_nhds ht)

theorem nse_gr_calculus_agree_on_positive_time (ν : ℝ) (u : Velocity) (p : Pressure)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    NSEGR.nseResidual ν u p t x =
      NSEMaxwell.Classical.timeDerivative u t x +
        NSEMaxwell.Classical.convection (u t) x +
        NSEMaxwell.Classical.gradient (p t) x -
        ν • NSEMaxwell.Classical.laplacian (u t) x := by
  rw [timeDerivative_eq_localTimeDerivative u ht x]
  rfl

def originNormalize (p : Pressure) : Pressure :=
  fun t x => p t x - p t 0

@[simp] theorem originNormalize_zero (p : Pressure) (t : ℝ) :
    originNormalize p t 0 = 0 := by simp [originNormalize]

@[simp] theorem originNormalize_idempotent (p : Pressure) :
    originNormalize (originNormalize p) = originNormalize p := by
  funext t x
  simp [originNormalize]

theorem originNormalize_gradient (p : Pressure) (t : ℝ) :
    NSEMaxwell.Classical.gradient (originNormalize p t) =
      NSEMaxwell.Classical.gradient (p t) := by
  funext x
  simp only [NSEMaxwell.Classical.gradient, originNormalize, fderiv_sub_const]

theorem originNormalize_smooth {p : Pressure}
    (hp : NSEMaxwell.Classical.SmoothPressure p) :
    NSEMaxwell.Classical.SmoothPressure (originNormalize p) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
    NSEMaxwell.Classical.forwardSpacetime at hp
  have hi : ContDiff ℝ ∞ (fun z : ℝ × Vec => (z.1, (0 : Vec))) :=
    contDiff_fst.prodMk contDiff_const
  have hzero : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 0)
      NSEMaxwell.Classical.forwardSpacetime := by
    simpa only [Function.comp_def] using
      hp.comp hi.contDiffOn (fun z hz => hz)
  exact hp.sub hzero

theorem originNormalize_periodic {p : Pressure}
    (hp : NSEMaxwell.Classical.PeriodicPressure p) :
    NSEMaxwell.Classical.PeriodicPressure (originNormalize p) := by
  intro t ht x i
  change p t (x + NSEMaxwell.Classical.unitVector i) - p t 0 = p t x - p t 0
  rw [hp t ht x i]

theorem nssolution_originNormalize {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) :
    NSEMaxwell.Classical.NSSolution ν a u (originNormalize p) := by
  refine {
    velocity_smooth := h.velocity_smooth
    pressure_smooth := originNormalize_smooth h.pressure_smooth
    velocity_periodic := h.velocity_periodic
    pressure_periodic := originNormalize_periodic h.pressure_periodic
    divergence_free := h.divergence_free
    equation := ?_
    initial := h.initial }
  intro t ht x
  rw [originNormalize_gradient]
  exact h.equation t ht x

theorem normalized_forward_pressure {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) :
    NSEMaxwell.Classical.NSSolution ν a u (originNormalize p) ∧
      ∀ t : ℝ, 0 ≤ t → originNormalize p t 0 = 0 := by
  exact ⟨nssolution_originNormalize h, fun t _ => originNormalize_zero p t⟩

def positiveSpacetime : Set (ℝ × Vec) := {z | 0 < z.1}

/-- Analyticity is an explicit local input; its global derivation is a separate goal. -/
structure PositiveAnalyticNSE (ν : ℝ) (u : Velocity) (p : Pressure) : Prop where
  velocity_analytic : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime
  pressure_analytic : AnalyticOnNhd ℝ (fun z : ℝ × Vec => p z.1 z.2) positiveSpacetime
  velocity_periodic : ∀ t : ℝ, 0 < t → SpatialPeriodic (u t)
  pressure_periodic : ∀ t : ℝ, 0 < t → SpatialPeriodic (p t)
  divergence_free : ∀ t : ℝ, 0 < t → ∀ x : Vec, divergence (u t) x = 0
  momentum : ∀ t : ℝ, 0 < t → ∀ x : Vec, nseResidual ν u p t x = 0

theorem positiveAnalyticNSE_of_nssolution
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime)
    (hp : AnalyticOnNhd ℝ (fun z : ℝ × Vec => p z.1 z.2) positiveSpacetime) :
    PositiveAnalyticNSE ν u p := by
  refine ⟨hu, hp, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact h.velocity_periodic t ht.le
  · intro t ht
    exact h.pressure_periodic t ht.le
  · intro t ht x
    exact h.divergence_free t ht.le x
  · intro t ht x
    rw [nse_gr_calculus_agree_on_positive_time ν u p ht x]
    exact sub_eq_zero.mpr (h.equation t ht.le x)

theorem half_timeInterval_positive {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ timeInterval τ (τ / 2)) : 0 < t := by
  change τ - τ / 2 < t ∧ t < τ + τ / 2 at ht
  linarith [ht.1]

def positiveTimeNSERepresentative {ν : ℝ} {u : Velocity} {p : Pressure}
    (h : PositiveAnalyticNSE ν u p) (τ : ℝ) (hτ : 0 < τ) : NSERepresentative ν τ where
  radius := τ / 2
  velocity := u
  pressure := p
  solution := {
    radius_pos := by positivity
    velocity_analytic := h.velocity_analytic.mono (by
      intro z hz
      exact half_timeInterval_positive hτ hz)
    pressure_analytic := h.pressure_analytic.mono (by
      intro z hz
      exact half_timeInterval_positive hτ hz)
    periodic_velocity := fun t ht => h.velocity_periodic t (half_timeInterval_positive hτ ht)
    periodic_pressure := fun t ht => h.pressure_periodic t (half_timeInterval_positive hτ ht)
    divergence_free := fun t ht => h.divergence_free t (half_timeInterval_positive hτ ht)
    momentum := fun t ht => h.momentum t (half_timeInterval_positive hτ ht) }

theorem positive_time_nse_representative {ν : ℝ} {u : Velocity} {p : Pressure}
    (h : PositiveAnalyticNSE ν u p) (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : NSERepresentative ν τ,
      n.velocity = u ∧ n.pressure = p ∧ n.radius = τ / 2 :=
  ⟨positiveTimeNSERepresentative h τ hτ, rfl, rfl, rfl⟩

end
end NSEGR.Strengthening
