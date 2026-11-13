import GRAssembly.NativeGaussianEvolutionExistence
import GRAssembly.NativeGaussianEvolutionCompatibilityJet
import GRAssembly.NativeGaussianEvolutionRicci
import GRAssembly.NativeGaussianEvolutionRecovery

/-! Deterministic assembly of the actual analytic Gaussian evolution. -/
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem gaussianStateSolutionMetric_tangential_vacuum
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), ∀ a b : Fin 4,
      ricci (gaussianMetric (gaussianStateSolutionMetric U)) z a.succ b.succ = 0 := by
  filter_upwards [(gaussianStateSolutionMetric_analyticAt hU).eventually_analyticAt,
    eventually_eventually_nhds.2 (gaussianStateSolutionMetric_symmetric hU),
    eventually_eventually_nhds.2 (gaussianStateSolutionMetric_nondegenerate hU),
    gaussianStateSolutionJet_compatible hU, gaussianStateSolutionMetric_secondRadial hU]
      with z hz hs hn hc hr
  exact (gaussianTangentialVacuum_iff_CKRHS hz hs hn hc).mpr hr

theorem gaussianEvolutionGerm_of_state
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U)
    (hS : ∀ᶠ y in 𝓝 (t0, x0), (K y.1 y.2).IsSymm) :
    GaussianEvolutionGerm K t0 x0 (gaussianStateSolutionMetric U) where
  analytic := gaussianStateSolutionMetric_analyticAt hU
  symmetric := gaussianStateSolutionMetric_symmetric hU
  nondegenerate := gaussianStateSolutionMetric_nondegenerate hU
  induced := gaussianStateSolutionMetric_induced hU
  boundary_match := gaussianStateSolutionMetric_boundary_match hU hS
  tangential_vacuum := gaussianStateSolutionMetric_tangential_vacuum hU

theorem gaussianEvolution_exists_of_CK (input : LiteratureAnalyticCKInput)
    (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec)
    (hK : AnalyticAt ℝ (fun y : GaussianBase => K y.1 y.2) (t0, x0))
    (hS : ∀ᶠ y in 𝓝 (t0, x0), (K y.1 y.2).IsSymm) :
    ∃ h : Bulk → Tensor4, GaussianEvolutionGerm K t0 x0 h := by
  obtain ⟨U, hU, _⟩ := gaussianEvolutionState_exists_unique input K t0 x0 hK
  exact ⟨gaussianStateSolutionMetric U, gaussianEvolutionGerm_of_state hU hS⟩

theorem gaussianEvolution_exists_unique_of_CK (input : LiteratureAnalyticCKInput)
    (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec)
    (hK : AnalyticAt ℝ (fun y : GaussianBase => K y.1 y.2) (t0, x0))
    (hS : ∀ᶠ y in 𝓝 (t0, x0), (K y.1 y.2).IsSymm) :
    ∃ h : Bulk → Tensor4, GaussianEvolutionGerm K t0 x0 h ∧
      ∀ q : Bulk → Tensor4, GaussianEvolutionGerm K t0 x0 q →
        h =ᶠ[𝓝 (bulkPoint 0 t0 x0)] q := by
  obtain ⟨U, hU, hUnique⟩ := gaussianEvolutionState_exists_unique input K t0 x0 hK
  exact ⟨gaussianStateSolutionMetric U, gaussianEvolutionGerm_of_state hU hS,
    fun _ hq => gaussianEvolutionGerm_unique_of_state_unique hUnique hq⟩

end
end NSEGR.NativeLiterature
