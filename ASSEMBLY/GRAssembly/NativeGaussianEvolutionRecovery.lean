import GRAssembly.NativeGaussianEvolutionCompatibility
import GRAssembly.NativeGaussianEvolutionRicci

/-! Recovery of the actual CK state from an analytic Gaussian evolution germ. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

def gaussianRecoveredState (h : Bulk → Tensor4) (p : ℝ × GaussianBase) : GaussianState :=
  ((h (gaussianBulkCoordinates p), coordDeriv h 0 (gaussianBulkCoordinates p)),
    fun a => coordDeriv h a.succ (gaussianBulkCoordinates p))

def gaussianRecoveredJet (h : Bulk → Tensor4) (p : ℝ × GaussianBase) :
    CKJet GaussianBase GaussianState :=
  (p, (gaussianRecoveredState h p,
    fderiv ℝ (fun y => gaussianRecoveredState h (p.1, y)) p.2))

theorem gaussianState_eq_of_components {u v : GaussianState}
    (hm : gaussianStateMetric u = gaussianStateMetric v)
    (hv : gaussianStateVelocity u = gaussianStateVelocity v)
    (hp : ∀ a, gaussianStateSpatial a u = gaussianStateSpatial a v) : u = v := by
  exact Prod.ext (Prod.ext hm hv) (funext hp)

theorem gaussianRecoveredState_analyticAt {h : Bulk → Tensor4} {p : ℝ × GaussianBase}
    (hh : AnalyticAt ℝ h (gaussianBulkCoordinates p)) :
    AnalyticAt ℝ (gaussianRecoveredState h) p := by
  have he := gaussianBulkCoordinates.analyticAt p
  apply ((hh.comp he).prod ((analyticAt_coordDeriv hh 0).comp he)).prod
  apply AnalyticAt.pi
  intro a
  exact (analyticAt_coordDeriv hh a.succ).comp he

theorem gaussianRecoveredJet_compatible {h : Bulk → Tensor4} {p : ℝ × GaussianBase}
    (hh : AnalyticAt ℝ h (gaussianBulkCoordinates p)) :
    GaussianJetCompatible h (gaussianBulkCoordinates p) (gaussianRecoveredJet h p) := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro a b
  have hU := gaussianRecoveredState_analyticAt hh
  have hs := hU.curry_right.differentiableAt
  change gaussianStateSpatial b
    (gaussianDirectional (fun y => gaussianRecoveredState h (p.1, y))
      (gaussianBaseBasis a) p.2) = _
  rw [← gaussianDirectional_clm (gaussianStateSpatial b) hs]
  change fderiv ℝ (fun y => coordDeriv h b.succ (gaussianBulkCoordinates (p.1, y)))
      p.2 (gaussianBaseBasis a) = _
  exact gaussianBulk_spaceDerivative (analyticAt_coordDeriv hh b.succ).differentiableAt a

theorem gaussianRecoveredState_metric (h : Bulk → Tensor4) :
    gaussianStateSolutionMetric (gaussianRecoveredState h) = h := by
  funext z
  change h (gaussianBulkCoordinates (gaussianSplitCoordinates z)) = h z
  rw [gaussianBulkCoordinates_split]

theorem gaussianRecoveredState_equation {h : Bulk → Tensor4} {p : ℝ × GaussianBase}
    (hh : AnalyticAt ℝ h (gaussianBulkCoordinates p))
    (hS : ∀ᶠ z in 𝓝 (gaussianBulkCoordinates p), (h z).IsSymm)
    (hN : ∀ᶠ z in 𝓝 (gaussianBulkCoordinates p), IsUnit (h z).det)
    (hR : ∀ a b : Fin 4,
      ricci (gaussianMetric h) (gaussianBulkCoordinates p) a.succ b.succ = 0) :
    ckTimeDerivative (gaussianRecoveredState h) p = gaussianCKRHS (gaussianRecoveredJet h p) := by
  have hU := gaussianRecoveredState_analyticAt hh
  have hC := gaussianRecoveredJet_compatible hh
  apply gaussianState_eq_of_components
  · rw [← gaussianTimeDerivative_clm gaussianStateMetric hU.differentiableAt]
    change ckTimeDerivative (fun q => h (gaussianBulkCoordinates q)) p =
      coordDeriv h 0 (gaussianBulkCoordinates p)
    exact gaussianBulk_timeDerivative hh.differentiableAt
  · rw [← gaussianTimeDerivative_clm gaussianStateVelocity hU.differentiableAt]
    change ckTimeDerivative (fun q => coordDeriv h 0 (gaussianBulkCoordinates q)) p = _
    rw [gaussianBulk_timeDerivative (analyticAt_coordDeriv hh 0).differentiableAt]
    exact (gaussianTangentialVacuum_iff_CKRHS hh hS hN hC).mp hR
  · intro a
    rw [← gaussianTimeDerivative_clm (gaussianStateSpatial a) hU.differentiableAt]
    change ckTimeDerivative (fun q => coordDeriv h a.succ (gaussianBulkCoordinates q)) p =
      gaussianStateVelocity
        (gaussianDirectional (fun y => gaussianRecoveredState h (p.1, y))
          (gaussianBaseBasis a) p.2)
    rw [gaussianBulk_timeDerivative (analyticAt_coordDeriv hh a.succ).differentiableAt,
      ← gaussianDirectional_clm gaussianStateVelocity hU.curry_right.differentiableAt]
    change coordDeriv (coordDeriv h a.succ) 0 (gaussianBulkCoordinates p) =
      fderiv ℝ (fun y => coordDeriv h 0 (gaussianBulkCoordinates (p.1, y)))
        p.2 (gaussianBaseBasis a)
    rw [gaussianBulk_spaceDerivative (analyticAt_coordDeriv hh 0).differentiableAt]
    exact coordDeriv_commute hh a.succ 0

theorem gaussianRecoveredState_initial {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {h : Bulk → Tensor4} (hE : GaussianEvolutionGerm K t0 x0 h) :
    ∀ᶠ y in 𝓝 (t0, x0), gaussianRecoveredState h (0, y) = gaussianInitialState K y := by
  have hb : Tendsto (fun y : GaussianBase => gaussianBulkCoordinates (0, y))
      (𝓝 (t0, x0)) (𝓝 (bulkPoint 0 t0 x0)) := by
    exact gaussianBulkCoordinates.continuous.continuousAt.tendsto.comp
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hi : (fun y : GaussianBase => h (gaussianBulkCoordinates (0, y))) =ᶠ[𝓝 (t0, x0)]
      (fun _ => eta4Matrix) := hE.induced
  filter_upwards [hE.induced, hE.boundary_match, hi.fderiv (𝕜 := ℝ),
    hb.eventually hE.analytic.eventually_analyticAt,
    hb.eventually (eventually_eventually_nhds.2 hE.symmetric)] with y hym hyk hyd hya hys
  apply gaussianState_eq_of_components
  · exact hym
  · change coordDeriv h 0 (gaussianBulkCoordinates (0, y)) =
      2 • gaussianSymmetrize (K y.1 y.2)
    have hk : (K y.1 y.2).IsSymm := by
      rw [← hyk, gaussianSecondForm_eq_half_radial hya]
      apply Matrix.IsSymm.ext
      intro a b
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul,
        (coordDeriv_tensor_symmetric hya hys 0).apply a b]
    rw [gaussianSymmetrize_eq_of_isSymm hk, ← hyk, gaussianSecondForm_eq_half_radial hya]
    ext a b
    simp only [two_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · intro a
    have hd0 : fderiv ℝ (fun q : GaussianBase => h (gaussianBulkCoordinates (0, q))) y = 0 := by
      simpa using hyd
    change coordDeriv h a.succ (gaussianBulkCoordinates (0, y)) = 0
    rw [← gaussianBulk_spaceDerivative hya.differentiableAt a, hd0]
    rfl

theorem gaussianRecoveredState_solution {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {h : Bulk → Tensor4} (hE : GaussianEvolutionGerm K t0 x0 h) :
    GaussianEvolutionStateSolution K t0 x0 (gaussianRecoveredState h) := by
  refine ⟨gaussianRecoveredState_analyticAt hE.analytic,
    gaussianRecoveredState_initial hE, ?_⟩
  have hb : Tendsto gaussianBulkCoordinates
      (𝓝 (0, (t0, x0))) (𝓝 (bulkPoint 0 t0 x0)) :=
    gaussianBulkCoordinates.continuous.continuousAt.tendsto
  filter_upwards [hb.eventually hE.analytic.eventually_analyticAt,
    hb.eventually (eventually_eventually_nhds.2 hE.symmetric),
    hb.eventually (eventually_eventually_nhds.2 hE.nondegenerate),
    hb.eventually hE.tangential_vacuum] with p hp hs hn hr
  exact gaussianRecoveredState_equation hp hs hn hr

theorem gaussianEvolutionGerm_unique_of_state_unique
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hUnique : ∀ V : ℝ × GaussianBase → GaussianState,
      GaussianEvolutionStateSolution K t0 x0 V → U =ᶠ[𝓝 (0, (t0, x0))] V)
    {h : Bulk → Tensor4} (hE : GaussianEvolutionGerm K t0 x0 h) :
    gaussianStateSolutionMetric U =ᶠ[𝓝 (bulkPoint 0 t0 x0)] h := by
  have hs := hUnique (gaussianRecoveredState h) (gaussianRecoveredState_solution hE)
  have hm : gaussianStateSolutionMetric U =ᶠ[𝓝 (bulkPoint 0 t0 x0)]
      gaussianStateSolutionMetric (gaussianRecoveredState h) := by
    filter_upwards [(gaussianSplit_tendsto t0 x0).eventually hs] with z hz
    exact congrArg gaussianStateMetric hz
  simpa only [gaussianRecoveredState_metric] using hm

end
end NSEGR.NativeLiterature
