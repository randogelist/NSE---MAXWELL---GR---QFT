import GRAdapter

/-! The forward implication composes actual scalar and radial completions. -/
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace NSEGR
noncomputable section

def chosenBoundary {ν ρ t0 : ℝ} (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (n : NSERepresentative ν t0) : CompletedBoundary ν ρ t0 n :=
  Classical.choice (c.complete n)

def chosenExtension {ν ρ t0 : ℝ} (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0) (n : NSERepresentative ν t0) :
    RadialExtensionResult ρ t0 (chosenBoundary c n).timeRadius (chosenBoundary c n).tensor :=
  Classical.choice (r.extend _ _ (chosenBoundary c n).admissible)

/-- A metric in the independent canonical sector, with every completion law explicit. -/
def forwardRepresentative {ν ρ t0 : ℝ} (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0) (n : NSERepresentative ν t0) :
    CanonicalRepresentative ν ρ t0 where
  timeRadius := (chosenExtension c r n).timeRadius
  radialRadius := (chosenExtension c r n).radialRadius
  metric := (chosenExtension c r n).metric
  geometry := (chosenExtension c r n).geometry
  stress_zero := by
    intro t ht x
    have hK := (chosenExtension c r n).boundary_match t ht
    rw [boundaryStress_congr_slice ν _ _ t hK]
    exact (chosenBoundary c n).stress_zero t
      (timeInterval_mono (chosenExtension c r n).time_radius_le ht) x

theorem forward_velocity_recovery {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (n : NSERepresentative ν t0) :
    ∀ᶠ t in 𝓝 t0,
      boundaryVelocity (boundaryK (forwardRepresentative c r n).metric) t = n.velocity t := by
  have hI := timeInterval_mem_nhds t0 (chosenExtension c r n).timeRadius
    (chosenExtension c r n).geometry.time_radius_pos
  filter_upwards [hI] with t ht
  change boundaryVelocity (boundaryK (chosenExtension c r n).metric) t = n.velocity t
  rw [boundaryVelocity_congr_slice _ _ t ((chosenExtension c r n).boundary_match t ht)]
  exact (chosenBoundary c n).velocity_recovery t
    (timeInterval_mono (chosenExtension c r n).time_radius_le ht)

theorem NSE_TO_GR_OF_SCALAR_AND_RADIAL_COMPLETION
    (ν ρ t0 : ℝ) (_hν : 0 < ν) (_hρ : ρ ≠ 0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (n : NSERepresentative ν t0) :
    ∃ g : CanonicalRepresentative ν ρ t0,
      ∀ᶠ t in 𝓝 t0, boundaryVelocity (boundaryK g.metric) t = n.velocity t :=
  ⟨forwardRepresentative c r n, forward_velocity_recovery c r n⟩

theorem nonempty_GRgerm_of_completion (ν ρ t0 : ℝ)
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0) :
    Nonempty (GRgerm ν ρ t0) :=
  ⟨GRgerm.mk (forwardRepresentative c r (constantNSERepresentative ν t0 0 0))⟩


/-- This conclusion uses the supplied radial extension's actual boundary match. -/
theorem forward_boundary_match_eventually {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0) (n : NSERepresentative ν t0) :
    boundaryK (forwardRepresentative c r n).metric =ᶠ[𝓝 t0]
      (chosenBoundary c n).tensor := by
  have hI := timeInterval_mem_nhds t0 (chosenExtension c r n).timeRadius
    (chosenExtension c r n).geometry.time_radius_pos
  filter_upwards [hI] with t ht
  exact (chosenExtension c r n).boundary_match t ht

/-- The entire decoded flow, including its pressure class, is recovered.
The decoded-left-inverse property needs no additional inverse-law premise. -/
theorem forward_pressure_gauge_recovery {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0) (n : NSERepresentative ν t0) :
    SameFlowAt t0
      (boundaryVelocity (boundaryK (forwardRepresentative c r n).metric))
      (boundaryPressure ρ (boundaryK (forwardRepresentative c r n).metric))
      n.velocity n.pressure := by
  have hlocal := boundaryFields_sameFlow_of_eventually_eq ρ
    (boundaryK (forwardRepresentative c r n).metric) (chosenBoundary c n).tensor
    (forward_boundary_match_eventually c r n)
  exact sameFlowAt_trans hlocal (chosenBoundary c n).pressure_recovery

end
end NSEGR
