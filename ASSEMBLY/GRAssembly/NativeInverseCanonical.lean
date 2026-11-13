import GRAssembly.NativeInverse
import GRAssembly.NativeReconstruction
import GRAssembly.BoundaryConstraints

/-!
Canonical metric reconstruction identifies the normalized scalar and the full
boundary tensor before invoking fixed-coordinate Gaussian uniqueness.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2000000

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Assembly
noncomputable section

/-- The independently defined canonical metric supplies an actual normalized scalar germ. -/
theorem canonical_scalarNormalGerm
    {ν ρ t0 : ℝ} (hρ : ρ ≠ 0)
    (g : CanonicalRepresentative ν ρ t0) (x0 : Vec) :
    ScalarNormalGerm ν ρ (boundaryVelocity (boundaryK g.metric))
      (boundaryPressure ρ (boundaryK g.metric)) t0 x0
      (boundaryPotential (boundaryK g.metric)) := by
  have hK := gaussianVacuum_boundaryAdmissible g.geometry
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 g.timeRadius :=
    timeInterval_mem_nhds t0 g.timeRadius g.geometry.time_radius_pos
  apply scalarNormalGerm_of_hamiltonian hρ
    (boundaryAdmissible_potential_analytic hK (t0, x0) ht.self_of_nhds)
    (Eventually.of_forall (boundaryAdmissible_potential_initial hK))
    (Eventually.of_forall (boundaryAdmissible_potential_time_initial hK))
  filter_upwards [ht.prod_inl_nhds x0] with z hz
  unfold boundaryHamiltonian
  rw [← canonical_boundary_exact_completion g z.1 hz]
  exact hK.hamiltonian z.1 hz z.2

/-- The selected scalar completion agrees with the original canonical boundary tensor. -/
theorem canonical_chosenBoundary_eventually
    (ck : LiteratureAnalyticCKInput) {ν ρ t0 : ℝ} (hρ : ρ ≠ 0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0)
    (g : CanonicalRepresentative ν ρ t0) :
    (chosenBoundary c (reverseRepresentative h g)).tensor =ᶠ[𝓝 t0]
      boundaryK g.metric := by
  let n := reverseRepresentative h g
  let cn := chosenBoundary c n
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 n.radius :=
    timeInterval_mem_nhds t0 n.radius n.solution.radius_pos
  have htc : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 cn.timeRadius :=
    timeInterval_mem_nhds t0 cn.timeRadius cn.admissible.radius_pos
  have hpot : cn.potential =ᶠ[𝓝 t0] boundaryPotential (boundaryK g.metric) := by
    have hp : ∀ᶠ t in 𝓝 t0,
        SpatialPeriodic (cn.potential t) ∧
          SpatialPeriodic (boundaryPotential (boundaryK g.metric) t) := by
      filter_upwards [htc] with t hct
      exact ⟨cn.potential_periodic t hct, poissonInverse_periodic _⟩
    have heq := periodic_slice_germs_uniform hp (fun x _ =>
      scalar_normalized_germ_unique ck hρ
        (n.solution.velocity_analytic (t0, x) ht.self_of_nhds)
        (n.solution.pressure_analytic (t0, x) ht.self_of_nhds)
        (completedBoundary_scalarNormalGerm cn hρ x)
        (canonical_scalarNormalGerm hρ g x))
    exact heq.mono (fun _ ht' => funext ht')
  change cn.tensor =ᶠ[𝓝 t0] boundaryK g.metric
  rw [cn.tensor_eq]
  have hcomp := completedBoundary_congr_eventually
    (ν := ν) (ρ := ρ)
    (EventuallyEq.rfl : n.velocity =ᶠ[𝓝 t0] n.velocity)
    (EventuallyEq.rfl : n.pressure =ᶠ[𝓝 t0] n.pressure) hpot
  apply hcomp.trans
  filter_upwards [ht] with t htt
  exact (canonical_boundary_exact_completion g t htt).symm

/-- Arbitrary completion and extension choices lift the decoded canonical metric back to itself. -/
theorem lift_decode_of_literature
    (ck : LiteratureAnalyticCKInput) (gj : LiteratureGaussianJetInput)
    {ν ρ t0 : ℝ} (hρ : ρ ≠ 0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0)
    (g : CanonicalRepresentative ν ρ t0) :
    SameMetricAt t0
      (forwardRepresentative c r (reverseRepresentative h g)).metric g.metric := by
  exact gaussianVacuum_sameMetricAt_of_literatureJet gj
    (chosenBoundary c (reverseRepresentative h g)).admissible
    (forwardRepresentative c r (reverseRepresentative h g)).geometry g.geometry
    (forward_boundary_match_eventually c r (reverseRepresentative h g))
    (canonical_chosenBoundary_eventually ck hρ c h g).symm

/-- Both inverse-law fields hold for arbitrary inhabitants of the three native records. -/
theorem germInverseLaws_of_literature
    (ck : LiteratureAnalyticCKInput) (gj : LiteratureGaussianJetInput)
    {ν ρ t0 : ℝ} (hρ : ρ ≠ 0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) : GermInverseLaws c r h where
  forward_respects := forward_respects_of_literature ck gj hρ c r
  lift_decode := lift_decode_of_literature ck gj hρ c r h

end
end NSEGR.Assembly
