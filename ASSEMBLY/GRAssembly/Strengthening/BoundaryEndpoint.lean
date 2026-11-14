import GRAssembly.Strengthening.ExactChain
import GRAssembly.Strengthening.PhysicalFourierNSE
import GRAssembly.Strengthening.SobolevNSETrace
import GRAssembly.Strengthening.SobolevPressureIdentification

/-!
# The velocity-trace boundary endpoint

The Sobolev witnesses in the exact spatial trace carry the actual physical
Fourier coefficients. Their positive-time norm equation is derived from the
physical NSE. The boundary equation, all-order time smoothness, joint synthesis,
and the normalized actual transport pressure then give the requested smooth
extension. No pressure trace or temporal trace is supplied.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Strengthening
noncomputable section

def profileSobolevCurve {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (m : ℕ) :
    ℝ → SingularClosure.TorusSobolev m :=
  (r.spatial_trace m).choose

theorem profileSobolevCurve_coeff_pos {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (profileSobolevCurve r m t).val = SingularClosure.datumFourierCoeff (r.velocity t) :=
  (r.spatial_trace m).choose_spec.1 ⟨t, ht⟩

theorem profileSobolevCurve_coeff_zero {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (m : ℕ) :
    (profileSobolevCurve r m 0).val = SingularClosure.datumFourierCoeff a :=
  (r.spatial_trace m).choose_spec.2.1

theorem profileSobolevCurve_trace {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (m : ℕ) :
    Tendsto (profileSobolevCurve r m) (𝓝[>] (0 : ℝ))
      (𝓝 (profileSobolevCurve r m 0)) :=
  (r.spatial_trace m).choose_spec.2.2

theorem profileSobolevCurve_eq_physical {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    profileSobolevCurve r m t = physicalFourierCurve m r.velocity t := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => r.velocity z.1 z.2) positiveSpacetime :=
    r.solution.velocity_analytic.contDiffOn_of_completeSpace
  have ht_smooth : ContDiff ℝ ∞ (r.velocity t) :=
    hs.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ht)
  apply Subtype.ext
  change (profileSobolevCurve r m t).val = (physicalFourierValue m (r.velocity t)).val
  rw [profileSobolevCurve_coeff_pos r m ht,
    physicalFourierValue_coeff m (r.velocity t) ht_smooth (r.solution.velocity_periodic t ht)]

theorem profileSobolevCurve_compatible {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) :
    ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      (profileSobolevCurve r m t).val = (profileSobolevCurve r 0 t).val := by
  intro m t ht
  by_cases hzero : t = 0
  · subst t
    rw [profileSobolevCurve_coeff_zero, profileSobolevCurve_coeff_zero]
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    rw [profileSobolevCurve_coeff_pos r m hpos, profileSobolevCurve_coeff_pos r 0 hpos]

/-- The trace witnesses inherit their actual Sobolev norm equation from physical NSE. -/
theorem profileSobolevCurve_hasDerivAt {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (profileSobolevCurve r m)
      (SingularClosure.fourierSobolevRhs ν m (profileSobolevCurve r (m + 2) t)) t := by
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => r.velocity z.1 z.2) positiveSpacetime :=
    r.solution.velocity_analytic.contDiffOn_of_completeSpace
  have hp : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => r.pressure z.1 z.2) positiveSpacetime :=
    r.solution.pressure_analytic.contDiffOn_of_completeSpace
  have hmom : ∀ s : ℝ, 0 < s → ∀ x,
      NSEMaxwell.Classical.timeDerivative r.velocity s x +
        SingularClosure.convection (r.velocity s) x + SingularClosure.gradient (r.pressure s) x =
          ν • SingularClosure.laplacian (r.velocity s) x := by
    intro s hs x
    have h := r.solution.momentum s hs x
    rw [nse_gr_calculus_agree_on_positive_time ν r.velocity r.pressure hs x] at h
    exact sub_eq_zero.mp h
  have hphysical := physical_NSE_fourierSobolev_hasDerivAt ν r.velocity r.pressure hu hp
    r.solution.velocity_periodic r.solution.pressure_periodic r.solution.divergence_free hmom m ht
  have heq : profileSobolevCurve r m =ᶠ[𝓝 t] physicalFourierCurve m r.velocity := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact profileSobolevCurve_eq_physical r m hs
  apply (hphysical.congr_of_eventuallyEq heq).congr_deriv
  rw [profileSobolevCurve_eq_physical r (m + 2) ht]

def profileBoundaryVelocity {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) : Velocity :=
  fun t x => SingularClosure.smoothFourierSynthesis (profileSobolevCurve r 0 t).val x

def profileBoundaryPressure {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) : Pressure :=
  normalizedSobolevPressure (profileSobolevCurve r)

theorem profileBoundaryVelocity_smooth {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) :
    NSEMaxwell.Classical.SmoothVelocity (profileBoundaryVelocity r) :=
  fourierNSE_forward_joint_smooth ν (profileSobolevCurve r) (profileSobolevCurve_trace r)
    (fun m _ ht => profileSobolevCurve_hasDerivAt r m ht) (profileSobolevCurve_compatible r)

theorem profileBoundaryPressure_smooth {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) :
    NSEMaxwell.Classical.SmoothPressure (profileBoundaryPressure r) :=
  fourierNSE_normalized_pressure_joint_smooth ν (profileSobolevCurve r)
    (profileSobolevCurve_trace r)
    (fun m _ ht => profileSobolevCurve_hasDerivAt r m ht) (profileSobolevCurve_compatible r)

theorem profileBoundaryVelocity_initial {ν : ℝ} {a : Field}
    (ha : NSEMaxwell.Classical.Data a) (r : PositiveProfileRepresentative ν a) :
    profileBoundaryVelocity r 0 = a := by
  change SingularClosure.smoothFourierSynthesis (profileSobolevCurve r 0 0).val = a
  rw [profileSobolevCurve_coeff_zero]
  exact physicalFourier_synthesis_eq a ha.smooth ha.periodic

theorem profileBoundaryVelocity_positive {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) {t : ℝ} (ht : 0 < t) :
    profileBoundaryVelocity r t = r.velocity t := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => r.velocity z.1 z.2) positiveSpacetime :=
    r.solution.velocity_analytic.contDiffOn_of_completeSpace
  have ht_smooth : ContDiff ℝ ∞ (r.velocity t) :=
    hs.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ht)
  change SingularClosure.smoothFourierSynthesis (profileSobolevCurve r 0 t).val = r.velocity t
  rw [profileSobolevCurve_coeff_pos r 0 ht]
  exact physicalFourier_synthesis_eq (r.velocity t) ht_smooth (r.solution.velocity_periodic t ht)

theorem profileBoundaryPressure_positive {ν : ℝ} {a : Field}
    (r : PositiveProfileRepresentative ν a) {t : ℝ} (ht : 0 < t) :
    profileBoundaryPressure r t = r.pressure t := by
  unfold profileBoundaryPressure normalizedSobolevPressure
  rw [profileSobolevCurve_eq_physical r 0 ht]
  change (fun x => SingularClosure.fullTransportPressure (physicalFourierValue 0 (r.velocity t)) x -
      SingularClosure.fullTransportPressure (physicalFourierValue 0 (r.velocity t)) 0) = r.pressure t
  rw [← positiveAnalyticNSE_normalized_pressure_eq_fullTransportPressure r.solution ht]
  funext x
  simp only [originNormalize, r.origin_normalized ⟨t, ht⟩, sub_zero]

/-- The exact boundary endpoint is derived from the velocity-only all-Sobolev trace. -/
theorem positiveProfileBoundaryEndpoint (ν : ℝ) (a : Field)
    (ha : NSEMaxwell.Classical.Data a) : PositiveProfileBoundaryEndpoint ν a := by
  intro r
  exact ⟨profileBoundaryVelocity r, profileBoundaryPressure r,
    profileBoundaryVelocity_smooth r, profileBoundaryPressure_smooth r,
    profileBoundaryVelocity_initial ha r,
    fun _ ht => ⟨profileBoundaryVelocity_positive r ht, profileBoundaryPressure_positive r ht⟩⟩

end
end NSEGR.Strengthening
