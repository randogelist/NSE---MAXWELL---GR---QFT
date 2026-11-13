import GRAssembly.NativeGaussianEvolutionCompatibility
import GRAssembly.NativeGaussianEvolutionJet

/-! The actual Gaussian evolution state supplies every field of jet compatibility. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
noncomputable section

def gaussianStateSolutionJet (U : ℝ × GaussianBase → GaussianState) (z : Bulk) :
    CKJet GaussianBase GaussianState :=
  (gaussianSplitCoordinates z,
    (U (gaussianSplitCoordinates z),
      fderiv ℝ (fun y => U ((gaussianSplitCoordinates z).1, y))
        (gaussianSplitCoordinates z).2))

theorem gaussianStateSolutionVelocity_radial
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      coordDeriv (gaussianStateSolutionVelocity U) 0 z =
        gaussianStateVelocity (gaussianCKRHS (gaussianStateSolutionJet U z)) := by
  filter_upwards [(gaussianSplit_tendsto t0 x0).eventually
      hU.analytic.eventually_analyticAt,
    (gaussianSplit_tendsto t0 x0).eventually hU.equation] with z hz he
  change gaussianDirectional
      (fun q => gaussianVelocityComponent U (gaussianSplitCoordinates q)) (bulkBasis 0) z = _
  have hv : DifferentiableAt ℝ (gaussianVelocityComponent U) (gaussianSplitCoordinates z) := by
    simpa only [gaussianVelocityComponent, Function.comp_def] using
      gaussianStateVelocity.differentiableAt.comp _ hz.differentiableAt
  rw [gaussianDirectional_comp_linear gaussianSplitCoordinates hv,
    gaussianSplitCoordinates_radial]
  change gaussianDirectional (fun q => gaussianStateVelocity (U q))
    (1, 0) (gaussianSplitCoordinates z) = _
  rw [gaussianDirectional_clm gaussianStateVelocity hz.differentiableAt]
  change gaussianStateVelocity (fderiv ℝ U (gaussianSplitCoordinates z) (1, 0)) = _
  rw [← ckTimeDerivative_eq_fderiv hz.differentiableAt]
  change gaussianStateVelocity
      (deriv (fun r => U (r, (gaussianSplitCoordinates z).2)) (gaussianSplitCoordinates z).1) = _
  rw [he]
  rfl

theorem gaussianStateSolutionMetric_secondRadial
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      coordDeriv (coordDeriv (gaussianStateSolutionMetric U) 0) 0 z =
        gaussianStateVelocity (gaussianCKRHS (gaussianStateSolutionJet U z)) := by
  have hrad : coordDeriv (gaussianStateSolutionMetric U) 0 =ᶠ[𝓝 (bulkPoint 0 t0 x0)]
      gaussianStateSolutionVelocity U := gaussianStateSolutionMetric_radial hU
  filter_upwards [gaussianDirectional_germ hrad (bulkBasis 0),
    gaussianStateSolutionVelocity_radial hU] with z hd hv
  exact hd.trans hv

theorem gaussianStateSolutionJet_second_derivative
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a b : Fin 4) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      gaussianJetSecond (gaussianStateSolutionJet U z) a b =
        coordDeriv (gaussianStateSolutionSpatial U b) a.succ z := by
  filter_upwards [(gaussianSplit_tendsto t0 x0).eventually
    hU.analytic.eventually_analyticAt] with z hz
  change gaussianStateSpatial b
      (fderiv ℝ (fun y => U ((gaussianSplitCoordinates z).1, y))
        (gaussianSplitCoordinates z).2 (gaussianBaseBasis a)) =
    gaussianDirectional
      (fun q => gaussianSpatialComponent U b (gaussianSplitCoordinates q))
      (bulkBasis a.succ) z
  rw [gaussianSpaceDerivative_eq_full hz.differentiableAt]
  have hs : DifferentiableAt ℝ (gaussianSpatialComponent U b)
      (gaussianSplitCoordinates z) := by
    simpa only [gaussianSpatialComponent, Function.comp_def] using
      (gaussianStateSpatial b).differentiableAt.comp _ hz.differentiableAt
  rw [gaussianDirectional_comp_linear gaussianSplitCoordinates hs,
    gaussianSplitCoordinates_tangent]
  exact (gaussianDirectional_clm (gaussianStateSpatial b)
    hz.differentiableAt (0, gaussianBaseBasis a)).symm

theorem gaussianStateSolutionJet_compatible
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      GaussianJetCompatible (gaussianStateSolutionMetric U) z (gaussianStateSolutionJet U z) := by
  have hs : ∀ a : Fin 4, ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      gaussianJetSpatial (gaussianStateSolutionJet U z) a =
        coordDeriv (gaussianStateSolutionMetric U) a.succ z := by
    intro a
    exact (gaussianStateSolutionMetric_spatial hU a).symm
  have hsecond : ∀ a b : Fin 4, ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      gaussianJetSecond (gaussianStateSolutionJet U z) a b =
        coordDeriv (coordDeriv (gaussianStateSolutionMetric U) b.succ) a.succ z := by
    intro a b
    have hp : gaussianStateSolutionSpatial U b =ᶠ[𝓝 (bulkPoint 0 t0 x0)]
        coordDeriv (gaussianStateSolutionMetric U) b.succ :=
      (gaussianStateSolutionMetric_spatial hU b).symm
    filter_upwards [gaussianStateSolutionJet_second_derivative hU a b,
      gaussianDirectional_germ hp (bulkBasis a.succ)] with z hz hd
    exact hz.trans hd
  filter_upwards [gaussianStateSolutionMetric_radial hU, Filter.eventually_all.mpr hs,
    Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (hsecond a))]
      with z hv hz hzz
  exact ⟨rfl, hv.symm, hz, hzz⟩

end
end NSEGR.NativeLiterature
