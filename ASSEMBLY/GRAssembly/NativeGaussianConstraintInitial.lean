import GRAssembly.NativeGaussianConstraintsPropagation
import GRAssembly.NativeGaussianEvolution

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem GaussianEvolutionGerm.eventually_at_boundary
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h) :
    ∀ᶠ y in 𝓝 (t0, x0), GaussianEvolutionGerm K y.1 y.2 h := by
  have hb : Tendsto (fun y : GaussianBase => bulkPoint 0 y.1 y.2)
      (𝓝 (t0, x0)) (𝓝 (bulkPoint 0 t0 x0)) := by
    exact Assembly.boundaryEmbed.continuous.continuousAt.tendsto
  filter_upwards [hE.analytic.eventually_analyticAt.comp_tendsto hb,
    (eventually_eventually_nhds.2 hE.symmetric).comp_tendsto hb,
    (eventually_eventually_nhds.2 hE.nondegenerate).comp_tendsto hb,
    eventually_eventually_nhds.2 hE.induced,
    eventually_eventually_nhds.2 hE.boundary_match,
    (eventually_eventually_nhds.2 hE.tangential_vacuum).comp_tendsto hb]
      with y ha hs hn hi hm ht
  exact ⟨ha, hs, hn, hi, hm, ht⟩

theorem flatBoundaryGerm_eventually {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    ∀ᶠ y in 𝓝 (t0, x0), LiteratureFlatBoundaryGerm K y.1 y.2 := by
  filter_upwards [hK.analytic.eventually_analyticAt,
    eventually_eventually_nhds.2 hK.symmetric,
    eventually_eventually_nhds.2 hK.hamiltonian,
    eventually_eventually_nhds.2 hK.codazzi] with y ha hs hh hc
  exact ⟨ha, hs, hh, hc⟩

theorem gaussianEvolution_tangential_jet_zero
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h) (a b c : Fin 4) :
    bulkPartial (fun y => h y a b) c.succ (bulkPoint 0 t0 x0) = 0 := by
  apply Assembly.bulkPartial_tangent_zero
    (Assembly.analyticAt_matrix_entry hE.analytic a b) (c := eta4 a b)
  exact hE.induced.mono (fun y hy => congrArg (fun M : Tensor4 => M a b) hy)

theorem gaussianEvolution_connection_zero
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h) (a b c : Fin 4) :
    gaussianTangentialChristoffel h (bulkPoint 0 t0 x0) a b c = 0 := by
  simp only [gaussianTangentialChristoffel, gaussianEvolution_tangential_jet_zero hE,
    zero_add, sub_zero, mul_zero, Finset.sum_const_zero]

theorem gaussianEvolution_connection_tangent_zero
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h) (a b c d : Fin 4) :
    bulkPartial (fun y => gaussianTangentialChristoffel h y a b c)
      d.succ (bulkPoint 0 t0 x0) = 0 := by
  apply Assembly.bulkPartial_tangent_zero
    (Assembly.analyticAt_gaussianTangentialChristoffel hE.analytic
      hE.nondegenerate.self_of_nhds a b c) (c := (0 : ℝ))
  exact hE.eventually_at_boundary.mono
    (fun y hy => gaussianEvolution_connection_zero hy a b c)

theorem gaussianResidualA_flat_of_tangential {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (he : h z = eta4Matrix) (hs : (gaussianSecondForm h z).IsSymm)
    (hc : ∀ a b c : Fin 4, gaussianTangentialChristoffel h z a b c = 0)
    (hdc : ∀ a b c d : Fin 4,
      bulkPartial (fun y => gaussianTangentialChristoffel h y a b c) d.succ z = 0)
    (hT : ∀ a b : Fin 4, ricci (gaussianMetric h) z a.succ b.succ = 0) :
    gaussianResidualA h z =
      -(lorentzSquare4 (gaussianSecondForm h z) -
        (lorentzTrace4 (gaussianSecondForm h z)) ^ 2) := by
  have hr := Assembly.gaussian_normal_flat hh hN.self_of_nhds he hs
  have ht (a : Fin 4) := Assembly.gaussian_tangential_flat hN he hs hc hdc a a
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have ht3 := ht 3
  rw [hT] at ht0 ht1 ht2 ht3
  have hs01 := hs.apply 0 1
  have hs02 := hs.apply 0 2
  have hs03 := hs.apply 0 3
  have hs12 := hs.apply 1 2
  have hs13 := hs.apply 1 3
  have hs23 := hs.apply 2 3
  norm_num [gaussianResidualA, lorentzTrace4, lorentzSquare4, Fin.sum_univ_four,
    lorentzSign4] at hr ht0 ht1 ht2 ht3 ⊢
  simp only [hs01, hs02, hs03, hs12, hs13, hs23] at hr ht0 ht1 ht2 ht3 ⊢
  linear_combination ht0 - ht1 - ht2 - ht3 + hr

theorem gaussianResidualA_initial_eq_hamiltonian
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h) :
    gaussianResidualA h (bulkPoint 0 t0 x0) = -boundaryHamiltonian K t0 x0 := by
  have he := gaussianResidualA_flat_of_tangential hE.analytic hE.nondegenerate
    hE.induced.self_of_nhds (gaussianSecondForm_symmetric hE.symmetric)
    (gaussianEvolution_connection_zero hE) (gaussianEvolution_connection_tangent_zero hE)
    hE.tangential_vacuum.self_of_nhds
  rw [hE.boundary_match.self_of_nhds] at he
  exact he

theorem gaussianEvolution_shape_boundary_derivative
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : AnalyticAt ℝ (fun y : GaussianBase => K y.1 y.2) (t0, x0))
    (a b c : Fin 4) :
    bulkPartial (fun y => gaussianShapeOperator h y a b) c.succ (bulkPoint 0 t0 x0) =
      lorentzSign4 a * boundaryPartial (fun t x => K t x a b) c t0 x0 := by
  have hs := Assembly.analyticAt_matrix_entry
    (Assembly.analyticAt_gaussianShape hE.analytic hE.nondegenerate.self_of_nhds) a b
  rw [← Assembly.boundaryPartial_restrict hs]
  have he :
      (fun y : GaussianBase => gaussianShapeOperator h (bulkPoint 0 y.1 y.2) a b) =ᶠ[𝓝 (t0, x0)]
      (fun y => lorentzSign4 a * K y.1 y.2 a b) := by
    filter_upwards [hE.induced, hE.boundary_match] with y hy hm
    rw [Assembly.gaussianShape_at_flat hy, hm]
  rw [Assembly.boundaryPartial_congr
    (f := fun t x => gaussianShapeOperator h (bulkPoint 0 t x) a b)
    (q := fun t x => lorentzSign4 a * K t x a b) he]
  exact Assembly.boundaryPartial_const_mul (Assembly.analyticAt_matrix_entry hK a b)
    (lorentzSign4 a) c

theorem gaussianResidualC_initial_eq_codazzi
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : AnalyticAt ℝ (fun y : GaussianBase => K y.1 y.2) (t0, x0))
    (a : Fin 4) :
    gaussianResidualC h (bulkPoint 0 t0 x0) a = boundaryCodazzi K t0 x0 a := by
  rw [gaussianResidualC, ricci_gaussian_mixed, Assembly.boundaryCodazzi_expanded hK]
  simp only [gaussianCodazziComponent, gaussianEvolution_shape_boundary_derivative hE hK,
    gaussianEvolution_connection_zero hE, zero_mul, sub_self,
    Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib]

theorem gaussian_constraints_initial_zero
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    gaussianResidualA h (bulkPoint 0 t0 x0) = 0 ∧
      ∀ a : Fin 4, gaussianResidualC h (bulkPoint 0 t0 x0) a = 0 := by
  constructor
  · rw [gaussianResidualA_initial_eq_hamiltonian hE, hK.hamiltonian.self_of_nhds, neg_zero]
  · intro a
    rw [gaussianResidualC_initial_eq_codazzi hE hK.analytic, hK.codazzi.self_of_nhds]

theorem gaussian_constraints_initial_zero_germ
    {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec} {h : Bulk → Tensor4}
    (hE : GaussianEvolutionGerm K t0 x0 h)
    (hK : LiteratureFlatBoundaryGerm K t0 x0) :
    ∀ᶠ y in 𝓝 (t0, x0),
      gaussianResidualA h (bulkPoint 0 y.1 y.2) = 0 ∧
      ∀ a : Fin 4, gaussianResidualC h (bulkPoint 0 y.1 y.2) a = 0 := by
  filter_upwards [hE.eventually_at_boundary, flatBoundaryGerm_eventually hK] with y he hk
  exact gaussian_constraints_initial_zero he hk

end
end NSEGR.NativeLiterature
