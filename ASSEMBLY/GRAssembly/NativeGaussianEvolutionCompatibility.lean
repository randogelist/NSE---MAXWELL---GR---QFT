import GRAssembly.NativeGaussianEvolution

/-! Native symmetry and spatial-jet compatibility of the actual Gaussian CK state. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

section DirectionalCalculus

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def gaussianDirectional (f : E → F) (v : E) (x : E) : F := fderiv ℝ f x v

theorem gaussianDirectional_analyticAt {f : E → F} {x : E}
    (hf : AnalyticAt ℝ f x) (v : E) :
    AnalyticAt ℝ (gaussianDirectional f v) x :=
  ((ContinuousLinearMap.apply ℝ F v).analyticAt _).comp hf.fderiv

theorem gaussianDirectional_clm (L : F →L[ℝ] G) {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    gaussianDirectional (fun y => L (f y)) v x = L (gaussianDirectional f v x) := by
  have hd := L.hasFDerivAt.comp x hf.hasFDerivAt
  have hd' : fderiv ℝ (fun y => L (f y)) x = L.comp (fderiv ℝ f x) := by
    simpa only [Function.comp_def] using hd.fderiv
  simp only [gaussianDirectional, hd', ContinuousLinearMap.comp_apply]

theorem gaussianDirectional_comp_linear (L : E →L[ℝ] G) {f : G → F} {x : E}
    (hf : DifferentiableAt ℝ f (L x)) (v : E) :
    gaussianDirectional (fun y => f (L y)) v x = gaussianDirectional f (L v) (L x) := by
  have hd := hf.hasFDerivAt.comp x L.hasFDerivAt
  have hd' : fderiv ℝ (fun y => f (L y)) x = (fderiv ℝ f (L x)).comp L := by
    simpa only [Function.comp_def] using hd.fderiv
  simp only [gaussianDirectional, hd', ContinuousLinearMap.comp_apply]

theorem gaussianDirectional_twice {f : E → F} {x : E}
    (hf : AnalyticAt ℝ f x) (v w : E) :
    gaussianDirectional (gaussianDirectional f v) w x =
      fderiv ℝ (fderiv ℝ f) x w v := by
  exact gaussianDirectional_clm (ContinuousLinearMap.apply ℝ F v)
    hf.fderiv.differentiableAt w

theorem gaussianDirectional_commute {f : E → F} {x : E}
    (hf : AnalyticAt ℝ f x) (v w : E) :
    gaussianDirectional (gaussianDirectional f v) w x =
      gaussianDirectional (gaussianDirectional f w) v x := by
  rw [gaussianDirectional_twice hf, gaussianDirectional_twice hf]
  exact (hf.contDiffAt (n := (2 : ℕ∞ω))).isSymmSndFDerivAt (by simp) w v

theorem gaussianDirectional_germ {f g : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] g) (v : E) :
    gaussianDirectional f v =ᶠ[𝓝 x] gaussianDirectional g v := by
  filter_upwards [h.fderiv] with y hy
  exact congrArg (fun L : E →L[ℝ] F => L v) hy

theorem gaussianTimeDerivative_clm (L : F →L[ℝ] G)
    {f : ℝ × E → F} {z : ℝ × E} (hf : DifferentiableAt ℝ f z) :
    ckTimeDerivative (fun y => L (f y)) z = L (ckTimeDerivative f z) := by
  rw [ckTimeDerivative_eq_fderiv (L.differentiableAt.comp z hf),
    ckTimeDerivative_eq_fderiv hf]
  exact gaussianDirectional_clm L hf (1, 0)

theorem gaussianSpaceDerivative_eq_full {f : ℝ × E → F} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ (fun y => f (z.1, y)) z.2 v = gaussianDirectional f (0, v) z := by
  simpa only [ckSpaceDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, gaussianDirectional] using
    congrArg (fun L : E →L[ℝ] F => L v) (ckSpaceDerivative_eq_fderiv hf)

/-- Local radial uniqueness uses the native one-dimensional mean-value theorem. -/
theorem gaussianGerm_eq_of_timeDerivative_eq {f g : ℝ × E → F} {r : ℝ} {y : E}
    (hf : AnalyticAt ℝ f (r, y)) (hg : AnalyticAt ℝ g (r, y))
    (hi : ∀ᶠ x in 𝓝 y, f (r, x) = g (r, x))
    (hd : ckTimeDerivative f =ᶠ[𝓝 (r, y)] ckTimeDerivative g) :
    f =ᶠ[𝓝 (r, y)] g := by
  have hp : ∀ᶠ z in 𝓝 r ×ˢ 𝓝 y,
      AnalyticAt ℝ f z ∧ AnalyticAt ℝ g z ∧
        ckTimeDerivative f z = ckTimeDerivative g z := by
    simpa only [nhds_prod_eq] using
      hf.eventually_analyticAt.and (hg.eventually_analyticAt.and hd)
  obtain ⟨ε, hε, p, hpy, hrect⟩ := Metric.eventually_nhds_prod_iff.mp hp
  rw [nhds_prod_eq]
  apply Metric.eventually_nhds_prod_iff.mpr
  refine ⟨ε, hε, (fun x => p x ∧ f (r, x) = g (r, x)), hpy.and hi, ?_⟩
  intro t ht x hx
  have hfd : DifferentiableOn ℝ (fun s : ℝ => f (s, x)) (Metric.ball r ε) := by
    intro s hs
    exact (hrect hs hx.1).1.curry_left.differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℝ (fun s : ℝ => g (s, x)) (Metric.ball r ε) := by
    intro s hs
    exact (hrect hs hx.1).2.1.curry_left.differentiableAt.differentiableWithinAt
  have hdeq : (Metric.ball r ε).EqOn
      (deriv (fun s => f (s, x))) (deriv (fun s => g (s, x))) := by
    intro s hs
    exact (hrect hs hx.1).2.2
  exact (Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball r ε).isPreconnected
    hfd hgd hdeq (by simpa using hε) hx.2) ht

end DirectionalCalculus

theorem gaussianBulkCoordinates_radial : gaussianBulkCoordinates (1, 0) = bulkBasis 0 := by
  ext i
  fin_cases i <;>
    norm_num [gaussianBulkCoordinates, bulkPoint, bulkBasis, EuclideanSpace.single]

theorem gaussianBulkCoordinates_tangent (a : Fin 4) :
    gaussianBulkCoordinates (0, gaussianBaseBasis a) = bulkBasis a.succ := by
  fin_cases a <;> ext i <;> fin_cases i <;>
    norm_num [gaussianBulkCoordinates, gaussianBaseBasis, bulkPoint, bulkBasis,
      unitVector, EuclideanSpace.single]

@[simp] theorem gaussianSplitCoordinates_bulkCoordinates (z : ℝ × GaussianBase) :
    gaussianSplitCoordinates (gaussianBulkCoordinates z) = z := by
  rcases z with ⟨r, t, x⟩
  exact gaussianSplitCoordinates_bulkPoint r t x

theorem gaussianSplitCoordinates_radial : gaussianSplitCoordinates (bulkBasis 0) = (1, 0) := by
  rw [← gaussianBulkCoordinates_radial, gaussianSplitCoordinates_bulkCoordinates]

theorem gaussianSplitCoordinates_tangent (a : Fin 4) :
    gaussianSplitCoordinates (bulkBasis a.succ) = (0, gaussianBaseBasis a) := by
  rw [← gaussianBulkCoordinates_tangent, gaussianSplitCoordinates_bulkCoordinates]

theorem gaussianBulk_timeDerivative {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : Bulk → F} {z : ℝ × GaussianBase}
    (hf : DifferentiableAt ℝ f (gaussianBulkCoordinates z)) :
    ckTimeDerivative (fun q => f (gaussianBulkCoordinates q)) z =
      fderiv ℝ f (gaussianBulkCoordinates z) (bulkBasis 0) := by
  rw [ckTimeDerivative_eq_fderiv (hf.comp z gaussianBulkCoordinates.differentiableAt)]
  change gaussianDirectional (fun q => f (gaussianBulkCoordinates q)) (1, 0) z = _
  rw [gaussianDirectional_comp_linear gaussianBulkCoordinates hf,
    gaussianBulkCoordinates_radial]
  rfl

theorem gaussianBulk_spaceDerivative {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : Bulk → F} {z : ℝ × GaussianBase}
    (hf : DifferentiableAt ℝ f (gaussianBulkCoordinates z)) (a : Fin 4) :
    fderiv ℝ (fun y => f (gaussianBulkCoordinates (z.1, y))) z.2 (gaussianBaseBasis a) =
      fderiv ℝ f (gaussianBulkCoordinates z) (bulkBasis a.succ) := by
  rw [gaussianSpaceDerivative_eq_full (hf.comp z gaussianBulkCoordinates.differentiableAt)]
  rw [gaussianDirectional_comp_linear gaussianBulkCoordinates hf,
    gaussianBulkCoordinates_tangent]
  rfl

def gaussianMetricComponent (U : ℝ × GaussianBase → GaussianState) :
    ℝ × GaussianBase → Tensor4 := fun z => gaussianStateMetric (U z)

def gaussianVelocityComponent (U : ℝ × GaussianBase → GaussianState) :
    ℝ × GaussianBase → Tensor4 := fun z => gaussianStateVelocity (U z)

def gaussianSpatialComponent (U : ℝ × GaussianBase → GaussianState) (a : Fin 4) :
    ℝ × GaussianBase → Tensor4 := fun z => gaussianStateSpatial a (U z)

variable {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
variable {U : ℝ × GaussianBase → GaussianState}

theorem gaussianMetricComponent_analyticAt
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    AnalyticAt ℝ (gaussianMetricComponent U) (0, (t0, x0)) :=
  (gaussianStateMetric.analyticAt _).comp hU.analytic

theorem gaussianVelocityComponent_analyticAt
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    AnalyticAt ℝ (gaussianVelocityComponent U) (0, (t0, x0)) :=
  (gaussianStateVelocity.analyticAt _).comp hU.analytic

theorem gaussianSpatialComponent_analyticAt
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a : Fin 4) :
    AnalyticAt ℝ (gaussianSpatialComponent U a) (0, (t0, x0)) :=
  ((gaussianStateSpatial a).analyticAt _).comp hU.analytic

theorem gaussianMetricComponent_timeDerivative
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ckTimeDerivative (gaussianMetricComponent U) =ᶠ[𝓝 (0, (t0, x0))]
      gaussianVelocityComponent U := by
  filter_upwards [hU.analytic.eventually_analyticAt, hU.equation] with z hz he
  change ckTimeDerivative (fun y => gaussianStateMetric (U y)) z = _
  rw [gaussianTimeDerivative_clm gaussianStateMetric hz.differentiableAt]
  change gaussianStateMetric (deriv (fun r => U (r, z.2)) z.1) = _
  rw [he]
  rfl

theorem gaussianMetricComponent_radial
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    gaussianDirectional (gaussianMetricComponent U) (1, 0) =ᶠ[𝓝 (0, (t0, x0))]
      gaussianVelocityComponent U := by
  filter_upwards [(gaussianMetricComponent_analyticAt hU).eventually_analyticAt,
    gaussianMetricComponent_timeDerivative hU] with z hz he
  exact (ckTimeDerivative_eq_fderiv hz.differentiableAt).symm.trans he

theorem gaussianSpatialComponent_timeDerivative
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a : Fin 4) :
    ckTimeDerivative (gaussianSpatialComponent U a) =ᶠ[𝓝 (0, (t0, x0))]
      gaussianDirectional (gaussianVelocityComponent U) (0, gaussianBaseBasis a) := by
  filter_upwards [hU.analytic.eventually_analyticAt, hU.equation] with z hz he
  change ckTimeDerivative (fun y => gaussianStateSpatial a (U y)) z = _
  rw [gaussianTimeDerivative_clm (gaussianStateSpatial a) hz.differentiableAt]
  change gaussianStateSpatial a (deriv (fun r => U (r, z.2)) z.1) = _
  rw [he, gaussianCKRHS_spatial]
  rw [gaussianSpaceDerivative_eq_full hz.differentiableAt]
  exact (gaussianDirectional_clm gaussianStateVelocity hz.differentiableAt
    (0, gaussianBaseBasis a)).symm

def gaussianSymmetryDefect : Tensor4 →L[ℝ] Tensor4 :=
  ContinuousLinearMap.id ℝ Tensor4 - gaussianSymmetrize

theorem gaussianSymmetryDefect_eq_zero {A : Tensor4} (hA : A.IsSymm) :
    gaussianSymmetryDefect A = 0 := by
  change A - gaussianSymmetrize A = 0
  rw [gaussianSymmetrize_eq_of_isSymm hA, sub_self]

theorem gaussianSymmetryDefect_zero_iff (A : Tensor4) :
    gaussianSymmetryDefect A = 0 ↔ A.IsSymm := by
  constructor
  · intro h
    have he : A = gaussianSymmetrize A := sub_eq_zero.mp h
    rw [he]
    exact gaussianSymmetrize_isSymm _
  · exact gaussianSymmetryDefect_eq_zero

theorem gaussianVelocityComponent_symmetric
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (0, (t0, x0)), (gaussianVelocityComponent U z).IsSymm := by
  let d := fun z => gaussianSymmetryDefect (gaussianVelocityComponent U z)
  have hd : AnalyticAt ℝ d (0, (t0, x0)) :=
    (gaussianSymmetryDefect.analyticAt _).comp (gaussianVelocityComponent_analyticAt hU)
  have hi : ∀ᶠ y in 𝓝 (t0, x0), d (0, y) = (0 : Tensor4) := by
    filter_upwards [hU.initial] with y hy
    change gaussianSymmetryDefect (gaussianStateVelocity (U (0, y))) = 0
    rw [hy]
    apply gaussianSymmetryDefect_eq_zero
    exact (gaussianSymmetrize_isSymm (K y.1 y.2)).smul 2
  have he : ckTimeDerivative d =ᶠ[𝓝 (0, (t0, x0))]
      ckTimeDerivative (fun _ : ℝ × GaussianBase => (0 : Tensor4)) := by
    filter_upwards [hU.analytic.eventually_analyticAt, hU.equation] with z hz he
    change ckTimeDerivative (fun y => gaussianSymmetryDefect
      (gaussianStateVelocity (U y))) z = _
    rw [gaussianTimeDerivative_clm gaussianSymmetryDefect
      (gaussianStateVelocity.differentiableAt.comp z hz.differentiableAt),
      gaussianTimeDerivative_clm gaussianStateVelocity hz.differentiableAt]
    change gaussianSymmetryDefect
      (gaussianStateVelocity (deriv (fun r => U (r, z.2)) z.1)) = _
    rw [he, gaussianSymmetryDefect_eq_zero (gaussianCKRHS_velocity_symmetric _)]
    simp [ckTimeDerivative]
  have hzero := gaussianGerm_eq_of_timeDerivative_eq hd analyticAt_const hi he
  filter_upwards [hzero] with z hz
  exact (gaussianSymmetryDefect_zero_iff _).mp hz

theorem gaussianMetricComponent_symmetric
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (0, (t0, x0)), (gaussianMetricComponent U z).IsSymm := by
  let d := fun z => gaussianSymmetryDefect (gaussianMetricComponent U z)
  have hd : AnalyticAt ℝ d (0, (t0, x0)) :=
    (gaussianSymmetryDefect.analyticAt _).comp (gaussianMetricComponent_analyticAt hU)
  have hi : ∀ᶠ y in 𝓝 (t0, x0), d (0, y) = (0 : Tensor4) := by
    filter_upwards [hU.initial] with y hy
    change gaussianSymmetryDefect (gaussianStateMetric (U (0, y))) = 0
    rw [hy]
    apply gaussianSymmetryDefect_eq_zero
    change eta4Matrix.IsSymm
    ext a b
    by_cases hab : a = b
    · subst b
      rfl
    · simp [eta4Matrix, eta4, hab, Ne.symm hab]
  have he : ckTimeDerivative d =ᶠ[𝓝 (0, (t0, x0))]
      ckTimeDerivative (fun _ : ℝ × GaussianBase => (0 : Tensor4)) := by
    filter_upwards [(gaussianMetricComponent_analyticAt hU).eventually_analyticAt,
      gaussianMetricComponent_timeDerivative hU, gaussianVelocityComponent_symmetric hU]
      with z hz he hs
    change ckTimeDerivative (fun y => gaussianSymmetryDefect
      (gaussianMetricComponent U y)) z = _
    rw [gaussianTimeDerivative_clm gaussianSymmetryDefect hz.differentiableAt,
      he, gaussianSymmetryDefect_eq_zero hs]
    simp [ckTimeDerivative]
  have hzero := gaussianGerm_eq_of_timeDerivative_eq hd analyticAt_const hi he
  filter_upwards [hzero] with z hz
  exact (gaussianSymmetryDefect_zero_iff _).mp hz

theorem gaussianSpatialComponent_eq_metricDerivative
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a : Fin 4) :
    gaussianSpatialComponent U a =ᶠ[𝓝 (0, (t0, x0))]
      gaussianDirectional (gaussianMetricComponent U) (0, gaussianBaseBasis a) := by
  let h := gaussianMetricComponent U
  let v := gaussianVelocityComponent U
  let P := gaussianSpatialComponent U a
  let e : ℝ × GaussianBase := (0, gaussianBaseBasis a)
  have hh : AnalyticAt ℝ h (0, (t0, x0)) := gaussianMetricComponent_analyticAt hU
  have hP : AnalyticAt ℝ P (0, (t0, x0)) := gaussianSpatialComponent_analyticAt hU a
  have hiH : (fun y => h (0, y)) =ᶠ[𝓝 (t0, x0)] (fun _ => eta4Matrix) := by
    filter_upwards [hU.initial] with y hy
    change gaussianStateMetric (U (0, y)) = eta4Matrix
    rw [hy]
    rfl
  have hboundary : Tendsto (fun y : GaussianBase => ((0 : ℝ), y))
      (𝓝 (t0, x0)) (𝓝 (0, (t0, x0))) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hi : ∀ᶠ y in 𝓝 (t0, x0), P (0, y) = gaussianDirectional h e (0, y) := by
    filter_upwards [hU.initial, hiH.fderiv,
      hboundary.eventually hh.eventually_analyticAt] with y hy hdy hay
    have hd0 : fderiv ℝ (fun x => h (0, x)) y = 0 := by simpa using hdy
    have hd := gaussianSpaceDerivative_eq_full hay.differentiableAt (gaussianBaseBasis a)
    change P (0, y) = gaussianDirectional h (0, gaussianBaseBasis a) (0, y)
    rw [← hd, hd0]
    change gaussianStateSpatial a (U (0, y)) = 0
    rw [hy]
    rfl
  have hdr : gaussianDirectional h (1, 0) =ᶠ[𝓝 (0, (t0, x0))] v :=
    gaussianMetricComponent_radial hU
  have hdre := gaussianDirectional_germ hdr e
  have he : ckTimeDerivative P =ᶠ[𝓝 (0, (t0, x0))]
      ckTimeDerivative (gaussianDirectional h e) := by
    filter_upwards [hh.eventually_analyticAt,
      gaussianSpatialComponent_timeDerivative hU a, hdre] with z hz hPz hez
    rw [hPz, ckTimeDerivative_eq_fderiv
      (gaussianDirectional_analyticAt hz e).differentiableAt]
    change gaussianDirectional v e z = gaussianDirectional (gaussianDirectional h e) (1, 0) z
    rw [gaussianDirectional_commute hz e (1, 0)]
    exact hez.symm
  exact gaussianGerm_eq_of_timeDerivative_eq hP (gaussianDirectional_analyticAt hh e) hi he

theorem gaussianSplit_tendsto (t : ℝ) (x : Vec) :
    Tendsto gaussianSplitCoordinates (𝓝 (bulkPoint 0 t x)) (𝓝 (0, (t, x))) := by
  have h : Tendsto gaussianSplitCoordinates (𝓝 (bulkPoint 0 t x))
      (𝓝 (gaussianSplitCoordinates (bulkPoint 0 t x))) :=
    gaussianSplitCoordinates.continuous.continuousAt.tendsto
  simpa only [gaussianSplitCoordinates_bulkPoint] using h

theorem gaussianStateSolutionMetric_radial
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      fderiv ℝ (gaussianStateSolutionMetric U) z (bulkBasis 0) =
        gaussianStateSolutionVelocity U z := by
  filter_upwards [(gaussianSplit_tendsto t0 x0).eventually
      (gaussianMetricComponent_analyticAt hU).eventually_analyticAt,
    (gaussianSplit_tendsto t0 x0).eventually (gaussianMetricComponent_radial hU)]
      with z hz he
  change gaussianDirectional (fun q => gaussianMetricComponent U (gaussianSplitCoordinates q))
    (bulkBasis 0) z = gaussianVelocityComponent U (gaussianSplitCoordinates z)
  rw [gaussianDirectional_comp_linear gaussianSplitCoordinates hz.differentiableAt,
    gaussianSplitCoordinates_radial]
  exact he

theorem gaussianStateSolutionMetric_spatial
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a : Fin 4) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      fderiv ℝ (gaussianStateSolutionMetric U) z (bulkBasis a.succ) =
        gaussianStateSolutionSpatial U a z := by
  filter_upwards [(gaussianSplit_tendsto t0 x0).eventually
      (gaussianMetricComponent_analyticAt hU).eventually_analyticAt,
    (gaussianSplit_tendsto t0 x0).eventually (gaussianSpatialComponent_eq_metricDerivative hU a)]
      with z hz he
  change gaussianDirectional (fun q => gaussianMetricComponent U (gaussianSplitCoordinates q))
    (bulkBasis a.succ) z = gaussianSpatialComponent U a (gaussianSplitCoordinates z)
  rw [gaussianDirectional_comp_linear gaussianSplitCoordinates hz.differentiableAt,
    gaussianSplitCoordinates_tangent]
  exact he.symm

theorem gaussianStateSolutionSpatial_radial
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a : Fin 4) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      fderiv ℝ (gaussianStateSolutionSpatial U a) z (bulkBasis 0) =
        fderiv ℝ (gaussianStateSolutionVelocity U) z (bulkBasis a.succ) := by
  filter_upwards [(gaussianSplit_tendsto t0 x0).eventually
      (gaussianSpatialComponent_analyticAt hU a).eventually_analyticAt,
    (gaussianSplit_tendsto t0 x0).eventually
      (gaussianVelocityComponent_analyticAt hU).eventually_analyticAt,
    (gaussianSplit_tendsto t0 x0).eventually (gaussianSpatialComponent_timeDerivative hU a)]
      with z hP hv he
  change gaussianDirectional (fun q => gaussianSpatialComponent U a (gaussianSplitCoordinates q))
      (bulkBasis 0) z =
    gaussianDirectional (fun q => gaussianVelocityComponent U (gaussianSplitCoordinates q))
      (bulkBasis a.succ) z
  rw [gaussianDirectional_comp_linear gaussianSplitCoordinates hP.differentiableAt,
    gaussianDirectional_comp_linear gaussianSplitCoordinates hv.differentiableAt,
    gaussianSplitCoordinates_radial, gaussianSplitCoordinates_tangent]
  exact (ckTimeDerivative_eq_fderiv hP.differentiableAt).symm.trans he

theorem gaussianStateSolutionVelocity_symmetric
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), (gaussianStateSolutionVelocity U z).IsSymm :=
  (gaussianSplit_tendsto t0 x0).eventually (gaussianVelocityComponent_symmetric hU)

theorem gaussianStateSolutionMetric_symmetric
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), (gaussianStateSolutionMetric U z).IsSymm :=
  (gaussianSplit_tendsto t0 x0).eventually (gaussianMetricComponent_symmetric hU)

theorem gaussianStateSolutionMetric_secondForm
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
      gaussianSecondForm (gaussianStateSolutionMetric U) z =
        (1 / 2 : ℝ) • gaussianStateSolutionVelocity U z := by
  filter_upwards [(gaussianStateSolutionMetric_analyticAt hU).eventually_analyticAt,
    gaussianStateSolutionMetric_radial hU] with z hz he
  ext a b
  change (1 / 2 : ℝ) *
      fderiv ℝ (fun q => gaussianStateSolutionMetric U q a b) z (bulkBasis 0) =
    (1 / 2 : ℝ) * gaussianStateSolutionVelocity U z a b
  rw [Assembly.matrix_entry_fderiv hz.differentiableAt, he]

theorem gaussianStateSolutionMetric_boundary_match
    (hU : GaussianEvolutionStateSolution K t0 x0 U)
    (hS : ∀ᶠ y in 𝓝 (t0, x0), (K y.1 y.2).IsSymm) :
    ∀ᶠ y in 𝓝 (t0, x0),
      gaussianSecondForm (gaussianStateSolutionMetric U) (bulkPoint 0 y.1 y.2) = K y.1 y.2 := by
  have hb : Tendsto Assembly.boundaryEmbed (𝓝 (t0, x0)) (𝓝 (bulkPoint 0 t0 x0)) :=
    Assembly.boundaryEmbed.continuous.continuousAt.tendsto
  filter_upwards [hb.eventually (gaussianStateSolutionMetric_secondForm hU),
    gaussianStateSolutionVelocity_initial hU hS] with y he hv
  change gaussianSecondForm (gaussianStateSolutionMetric U) (bulkPoint 0 y.1 y.2) = _
  change gaussianSecondForm (gaussianStateSolutionMetric U) (bulkPoint 0 y.1 y.2) =
    (1 / 2 : ℝ) • gaussianStateSolutionVelocity U (bulkPoint 0 y.1 y.2) at he
  rw [he, hv]
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

end
end NSEGR.NativeLiterature
