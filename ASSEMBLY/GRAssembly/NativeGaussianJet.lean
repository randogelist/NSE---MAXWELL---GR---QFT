import GRAssembly.NativeGaussianConstraintZero
import GRAssembly.NativeGaussianEvolutionAssembly
import GRAssembly.BoundaryConstraints

/-! Exact prescribed-data Gaussian vacuum germs from the literal analytic CK input. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem literatureFlatGaussianGerm_of_evolution (input : LiteratureAnalyticCKInput)
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    LiteratureFlatGaussianGerm K t0 x0 (gaussianMetric h) where
  analytic := analyticAt_gaussianBlockMetric hE.analytic
  symmetric := hE.symmetric.mono (fun _ hy => gaussianBlockMetric_symmetric hy)
  nondegenerate := hE.nondegenerate.mono
    (fun _ hy => isUnit_iff_ne_zero.mp (gaussianBlockMetric_unit hy))
  gaussian_rr := Filter.Eventually.of_forall (fun z => gaussianMetric_rr h z)
  gaussian_rboundary := Filter.Eventually.of_forall (fun z a => gaussianMetric_rb h z a)
  induced := by
    filter_upwards [hE.induced] with y hy
    intro a b
    change h (bulkPoint 0 y.1 y.2) a b = eta4 a b
    exact congrArg (fun M : Tensor4 => M a b) hy
  boundary_match := hE.boundary_match
  vacuum := gaussianEvolution_vacuum_of_constraints input hE hK

theorem literatureFlatGaussianGerm_exists_of_analyticCK (input : LiteratureAnalyticCKInput)
    (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    ∃ g : Metric, LiteratureFlatGaussianGerm K t0 x0 g := by
  obtain ⟨h, hE⟩ := gaussianEvolution_exists_of_CK input K t0 x0 hK.analytic hK.symmetric
  exact ⟨gaussianMetric h, literatureFlatGaussianGerm_of_evolution input hE hK⟩

theorem literatureFlatGaussianGerm_eq_gaussian
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {g : Metric}
    (hg : LiteratureFlatGaussianGerm K t0 x0 g) :
    g =ᶠ[𝓝 (bulkPoint 0 t0 x0)] gaussianMetric (Assembly.metricTangentialBlock g) := by
  filter_upwards [hg.gaussian_rr, hg.gaussian_rboundary, hg.symmetric] with z hrr hrb hs
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases hrr (fun j => hrb j) b
  · refine Fin.cases ?_ (fun j => rfl) b
    exact (hs.apply 0 i.succ).trans (hrb i)

theorem literatureFlatGaussianGerm_evolution
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {g : Metric}
    (hg : LiteratureFlatGaussianGerm K t0 x0 g) :
    GaussianEvolutionGerm K t0 x0 (Assembly.metricTangentialBlock g) where
  analytic := by
    apply Assembly.analyticAt_matrix_of_entries
    intro a b
    exact Assembly.analyticAt_matrix_entry hg.analytic a.succ b.succ
  symmetric := by
    filter_upwards [hg.symmetric] with z hz
    apply Matrix.IsSymm.ext
    intro a b
    exact hz.apply a.succ b.succ
  nondegenerate := by
    filter_upwards [hg.nondegenerate, literatureFlatGaussianGerm_eq_gaussian hg] with z hn he
    apply isUnit_iff_ne_zero.mpr
    rw [← gaussianMatrix_det]
    change (gaussianMetric (Assembly.metricTangentialBlock g) z).det ≠ 0
    rwa [← he]
  induced := by
    filter_upwards [hg.induced] with y hy
    ext a b
    exact hy a b
  boundary_match := hg.boundary_match
  tangential_vacuum := by
    filter_upwards [(literatureFlatGaussianGerm_eq_gaussian hg).eventuallyEq_nhds,
      hg.vacuum] with z he hv
    intro a b
    rw [← Assembly.ricci_metric_germ he, hv]
    rfl

/-- Literal LI02: analytic CK alone constructs and uniquely determines the
prescribed Gaussian vacuum metric germ in the same coordinates. -/
theorem literatureGaussianJetInput_of_analyticCK (input : LiteratureAnalyticCKInput) :
    LiteratureGaussianJetInput := by
  constructor
  intro K t0 x0 hK
  obtain ⟨h, hE, hUnique⟩ := gaussianEvolution_exists_unique_of_CK
    input K t0 x0 hK.analytic hK.symmetric
  refine ⟨gaussianMetric h, literatureFlatGaussianGerm_of_evolution input hE hK, ?_⟩
  intro g hg
  have he := hUnique (Assembly.metricTangentialBlock g)
    (literatureFlatGaussianGerm_evolution hg)
  filter_upwards [he, literatureFlatGaussianGerm_eq_gaussian hg] with z hz hzg
  change gaussianMatrix (h z) = g z
  rw [hz]
  exact hzg.symm

end
end NSEGR.NativeLiterature
