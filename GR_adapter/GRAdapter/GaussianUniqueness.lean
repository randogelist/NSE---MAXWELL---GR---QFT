import GRAdapter.LiteratureInputs
import GRAdapter.GermUniformity

/-!
# Native fixed-marking Gaussian uniqueness from LI02

The only literature premise is LiteratureGaussianJetInput. Independently
admissible boundary data and actual Gaussian vacua are translated into its
point-local hypotheses. Compact periodic uniformization then gives the native
full-spatial SameMetricAt relation. Radial existence and gluing remain separate.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace NSEGR
noncomputable section

theorem bulkCollar_eventually_boundary {t0 δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (x0 : Vec) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), z ∈ bulkCollar t0 δ ε := by
  have hr : ∀ᶠ r in 𝓝 (0 : ℝ), r ∈ Ioo (-ε) ε := by
    apply Ioo_mem_nhds <;> linarith
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 δ := by
    apply Ioo_mem_nhds <;> linarith
  have hc : Continuous (fun z : Bulk => (z 0, z 1)) := by fun_prop
  have hp : Tendsto (fun z : Bulk => (z 0, z 1))
      (𝓝 (bulkPoint 0 t0 x0)) (𝓝 ((0 : ℝ), t0)) := by
    simpa only [bulkPoint_radial, bulkPoint_time] using hc.tendsto (bulkPoint 0 t0 x0)
  exact hp.eventually (hr.prodMk_nhds ht)

/-- The native constrained tensor provides exactly LI02's boundary hypotheses. -/
theorem boundaryAdmissible_literatureFlatBoundaryGerm
    {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) (x0 : Vec) :
    LiteratureFlatBoundaryGerm K t0 x0 := by
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 δ := by
    apply Ioo_mem_nhds <;> linarith [hK.radius_pos]
  have hslab := ht.prod_inl_nhds x0
  refine {
    analytic := hK.analytic (t0, x0) ht.self_of_nhds
    symmetric := ?_
    hamiltonian := ?_
    codazzi := ?_ }
  · filter_upwards [hslab] with z hz
    exact hK.symmetric z.1 hz z.2
  · filter_upwards [hslab] with z hz
    exact hK.hamiltonian z.1 hz z.2
  · filter_upwards [hslab] with z hz
    exact hK.momentum_constraint z.1 hz z.2

/-- Actual collar geometry and an actual normal-jet time germ provide LI02's metric germ. -/
theorem gaussianVacuum_literatureFlatGaussianGerm
    {ρ t0 δ ε : ℝ} {K : BoundaryTensor} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g)
    (hmatch : boundaryK g =ᶠ[𝓝 t0] K) (x0 : Vec) :
    LiteratureFlatGaussianGerm K t0 x0 g := by
  have hb := bulkCollar_eventually_boundary (t0 := t0)
    hg.time_radius_pos hg.radial_radius_pos x0
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 δ := by
    apply Ioo_mem_nhds <;> linarith [hg.time_radius_pos]
  refine {
    analytic := hg.analytic (bulkPoint 0 t0 x0) hb.self_of_nhds
    symmetric := hb.mono (fun z hz => hg.symmetric z hz)
    nondegenerate := hb.mono (fun z hz => gaussianVacuum_nondegenerate hg z hz)
    gaussian_rr := hb.mono (fun z hz => hg.gaussian_rr z hz)
    gaussian_rboundary := hb.mono (fun z hz => hg.gaussian_rboundary z hz)
    induced := ?_
    boundary_match := ?_
    vacuum := hb.mono (fun z hz => hg.vacuum z hz) }
  · filter_upwards [ht.prod_inl_nhds x0] with z hz
    exact hg.induced z.1 hz z.2
  · filter_upwards [hmatch.prod_inl_nhds x0] with z hz
    exact congrFun hz z.2

/-- Two literal prescribed-data Gaussian germs coincide under LI02. -/
theorem literatureGaussianJet_unique (input : LiteratureGaussianJetInput)
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {g h : Metric}
    (hK : LiteratureFlatBoundaryGerm K t0 x0)
    (hg : LiteratureFlatGaussianGerm K t0 x0 g)
    (hh : LiteratureFlatGaussianGerm K t0 x0 h) :
    g =ᶠ[𝓝 (bulkPoint 0 t0 x0)] h := by
  obtain ⟨u, hu, hunique⟩ := input.exists_unique K t0 x0 hK
  exact (hunique g hg).symm.trans (hunique h hh)

/-- Native full-spatial uniqueness for independently constrained common boundary data.
Only the source-facing LI02 theorem remains a literature premise. -/
theorem gaussianVacuum_sameMetricAt_of_literatureJet
    (input : LiteratureGaussianJetInput)
    {ρK ρg ρh t0 δK δg εg δh εh : ℝ} {K : BoundaryTensor} {g h : Metric}
    (hK : BoundaryAdmissible ρK t0 δK K)
    (hg : GaussianVacuum ρg t0 δg εg g) (hh : GaussianVacuum ρh t0 δh εh h)
    (hgmatch : boundaryK g =ᶠ[𝓝 t0] K)
    (hhmatch : boundaryK h =ᶠ[𝓝 t0] K) :
    SameMetricAt t0 g h := by
  apply gaussianVacuum_sameMetricAt_of_boundary_germs hg hh
  intro x hx
  exact literatureGaussianJet_unique input
    (boundaryAdmissible_literatureFlatBoundaryGerm hK x)
    (gaussianVacuum_literatureFlatGaussianGerm hg hgmatch x)
    (gaussianVacuum_literatureFlatGaussianGerm hh hhmatch x)

end
end NSEGR
