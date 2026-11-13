import GRAssembly.NativeGaussianContraction

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem analyticAt_gaussianBlockMetric {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) : AnalyticAt ℝ (gaussianMetric h) z := by
  apply Assembly.analyticAt_matrix_of_entries
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · exact analyticAt_const
    · exact analyticAt_const
  · refine Fin.cases ?_ (fun b => ?_) j
    · exact analyticAt_const
    · exact Assembly.analyticAt_matrix_entry hh a b

theorem gaussianBlockMetric_symmetric {h : Bulk → Tensor4} {z : Bulk}
    (hS : (h z).IsSymm) : (gaussianMetric h z).IsSymm := by
  change (gaussianMatrix (h z)).transpose = gaussianMatrix (h z)
  rw [← gaussianMatrix_transpose, hS.eq]

theorem gaussianBlockMetric_unit {h : Bulk → Tensor4} {z : Bulk}
    (hN : IsUnit (h z).det) : IsUnit (gaussianMetric h z).det := by
  simpa only [gaussianMetric, gaussianMatrix_det] using hN

theorem gaussianSecondForm_symmetric {h : Bulk → Tensor4} {z : Bulk}
    (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm) : (gaussianSecondForm h z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold gaussianSecondForm
  congr 1
  apply Assembly.bulkPartial_congr_of_eventuallyEq
  exact hS.mono (fun y hy => hy.apply a b)

theorem gaussianRicci_symmetric_eventually {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) :
    ∀ᶠ y in 𝓝 z, (ricci (gaussianMetric h) y).IsSymm := by
  filter_upwards [hh.eventually_analyticAt, eventually_eventually_nhds.2 hS,
    eventually_eventually_nhds.2 hN] with y hy hs hn
  exact nativeRicci_symmetric (analyticAt_gaussianBlockMetric hy)
    (hs.mono (fun q hq => gaussianBlockMetric_symmetric hq))
    (hn.mono (fun q hq => gaussianBlockMetric_unit hq))

def gaussianResidualA (h : Bulk → Tensor4) (z : Bulk) : ℝ :=
  ricci (gaussianMetric h) z 0 0

def gaussianResidualC (h : Bulk → Tensor4) (z : Bulk) (a : Fin 4) : ℝ :=
  ricci (gaussianMetric h) z 0 a.succ

def gaussianKappa (h : Bulk → Tensor4) (z : Bulk) : ℝ :=
  ∑ a : Fin 4, gaussianShapeOperator h z a a

def gaussianResidualDivergence (h : Bulk → Tensor4) (z : Bulk) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, (h z)⁻¹ a b *
    (bulkPartial (fun y => gaussianResidualC h y b) a.succ z -
      ∑ c : Fin 4, gaussianTangentialChristoffel h z c a b * gaussianResidualC h z c)

def nativeRicciDivergence (g : Metric) (z : Bulk) (e : Fin 5) : ℝ :=
  ∑ a : Fin 5, ∑ c : Fin 5, (g z)⁻¹ a c * covariantRicci g z a c e

theorem gaussian_scalarCurvature_eq_residual {h : Bulk → Tensor4} {z : Bulk}
    (hN : IsUnit (h z).det)
    (hT : ∀ a b : Fin 4, ricci (gaussianMetric h) z a.succ b.succ = 0) :
    scalarCurvature (gaussianMetric h) z = gaussianResidualA h z := by
  simp only [scalarCurvature, inverseMetric_gaussian h z hN,
    Fin.sum_univ_succ, gaussianMatrix_rr, gaussianMatrix_rb, gaussianMatrix_ar,
    gaussianMatrix_ab, hT, one_mul, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, gaussianResidualA]

theorem gaussian_scalarCurvature_derivative {h : Bulk → Tensor4} {z : Bulk}
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hT : ∀ᶠ y in 𝓝 z, ∀ a b : Fin 4,
      ricci (gaussianMetric h) y a.succ b.succ = 0) (i : Fin 5) :
    bulkPartial (scalarCurvature (gaussianMetric h)) i z =
      bulkPartial (gaussianResidualA h) i z := by
  apply Assembly.bulkPartial_congr_of_eventuallyEq
  filter_upwards [hN, hT] with y hn ht
  exact gaussian_scalarCurvature_eq_residual hn ht

theorem gaussianRicciDivergence_split {h : Bulk → Tensor4} {z : Bulk}
    (hN : IsUnit (h z).det) (e : Fin 5) :
    nativeRicciDivergence (gaussianMetric h) z e =
      covariantRicci (gaussianMetric h) z 0 0 e +
      ∑ a : Fin 4, ∑ b : Fin 4, (h z)⁻¹ a b *
        covariantRicci (gaussianMetric h) z a.succ b.succ e := by
  change (∑ a : Fin 5, ∑ c : Fin 5,
    inverseMetric (gaussianMetric h) z a c * covariantRicci (gaussianMetric h) z a c e) = _
  rw [inverseMetric_gaussian h z hN]
  simp only [Fin.sum_univ_succ, gaussianMatrix_rr, gaussianMatrix_rb,
    gaussianMatrix_ar, gaussianMatrix_ab, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add]

theorem gaussianCovariantRicci_rrr {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) :
    covariantRicci (gaussianMetric h) z 0 0 0 =
      bulkPartial (gaussianResidualA h) 0 z := by
  have hr := analyticAt_nativeRicci (analyticAt_gaussianBlockMetric hh)
    (gaussianBlockMetric_unit hN)
  unfold covariantRicci
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, metricConnection,
    christoffel_gaussian_rr, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  exact coordDeriv_matrix_entry hr 0 0 0

theorem gaussianCovariantRicci_rra {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) (i : Fin 4) :
    covariantRicci (gaussianMetric h) z 0 0 i.succ =
      bulkPartial (fun y => gaussianResidualC h y i) 0 z -
        ∑ c : Fin 4, gaussianResidualC h z c * gaussianShapeOperator h z c i := by
  have hr := analyticAt_nativeRicci (analyticAt_gaussianBlockMetric hh)
    (gaussianBlockMetric_unit hN)
  unfold covariantRicci
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, metricConnection,
    christoffel_gaussian_rr, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [coordDeriv_matrix_entry hr]
  simp only [Fin.sum_univ_succ, christoffel_gaussian_rrb_total,
    christoffel_gaussian_shape, mul_zero, zero_add, gaussianResidualC]

theorem gaussianCovariantRicci_abr {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hT : ∀ a b : Fin 4, ricci (gaussianMetric h) z a.succ b.succ = 0)
    (a b : Fin 4) :
    covariantRicci (gaussianMetric h) z a.succ b.succ 0 =
      bulkPartial (fun y => gaussianResidualC h y b) a.succ z -
        (∑ c : Fin 4, gaussianTangentialChristoffel h z c a b * gaussianResidualC h z c) +
        gaussianSecondForm h z a b * gaussianResidualA h z := by
  have hr := analyticAt_nativeRicci (analyticAt_gaussianBlockMetric hh)
    (gaussianBlockMetric_unit hN.self_of_nhds)
  have hs := gaussianRicci_symmetric_eventually hh hS hN
  have hm (c : Fin 4) : ricci (gaussianMetric h) z c.succ 0 = gaussianResidualC h z c :=
    hs.self_of_nhds.apply 0 c.succ
  unfold covariantRicci
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, metricConnection]
  rw [coordDeriv_matrix_entry hr,
    bulkPartial_entry_symm hs a.succ 0 b.succ]
  simp only [Fin.sum_univ_succ, christoffel_gaussian_rab h z hN.self_of_nhds,
    christoffel_gaussian_abc_total, Assembly.christoffel_gaussian_rbr_total,
    Assembly.christoffel_gaussian_abr_total, hT, hm, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, gaussianResidualA, gaussianResidualC]
  ring

theorem gaussianCovariantRicci_abi {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hT : ∀ᶠ y in 𝓝 z, ∀ a b : Fin 4,
      ricci (gaussianMetric h) y a.succ b.succ = 0) (a b i : Fin 4) :
    covariantRicci (gaussianMetric h) z a.succ b.succ i.succ =
      gaussianSecondForm h z a b * gaussianResidualC h z i +
        gaussianSecondForm h z a i * gaussianResidualC h z b := by
  have hr := analyticAt_nativeRicci (analyticAt_gaussianBlockMetric hh)
    (gaussianBlockMetric_unit hN.self_of_nhds)
  have hs := gaussianRicci_symmetric_eventually hh hS hN
  have hm (c : Fin 4) : ricci (gaussianMetric h) z c.succ 0 = gaussianResidualC h z c :=
    hs.self_of_nhds.apply 0 c.succ
  have hd : bulkPartial
      (fun y => ricci (gaussianMetric h) y b.succ i.succ) a.succ z = 0 := by
    have he : (fun y => ricci (gaussianMetric h) y b.succ i.succ) =ᶠ[𝓝 z]
        (fun _ => (0 : ℝ)) := hT.mono (fun y hy => hy b i)
    rw [Assembly.bulkPartial_congr_of_eventuallyEq _ _ _ he, bulkPartial_const]
  unfold covariantRicci
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, metricConnection]
  rw [coordDeriv_matrix_entry hr, hd]
  simp only [Fin.sum_univ_succ, christoffel_gaussian_rab h z hN.self_of_nhds,
    christoffel_gaussian_abc_total, hT.self_of_nhds, hm, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, gaussianResidualC]
  ring

theorem gaussianSecondForm_trace_contraction {h : Bulk → Tensor4} {z : Bulk}
    (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm) :
    (∑ a : Fin 4, ∑ b : Fin 4, (h z)⁻¹ a b * gaussianSecondForm h z a b) =
      gaussianKappa h z := by
  unfold gaussianKappa gaussianShapeOperator
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [(gaussianSecondForm_symmetric hS).apply a b]

theorem gaussianShape_contraction {h : Bulk → Tensor4} {z : Bulk}
    (hS : (h z).IsSymm) (i : Fin 4) :
    (∑ a : Fin 4, ∑ b : Fin 4,
      (h z)⁻¹ a b * (gaussianSecondForm h z a i * gaussianResidualC h z b)) =
      ∑ b : Fin 4, gaussianResidualC h z b * gaussianShapeOperator h z b i := by
  have hI : ((h z)⁻¹).IsSymm := by
    change ((h z)⁻¹).transpose = (h z)⁻¹
    rw [Matrix.transpose_nonsing_inv, hS.eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  unfold gaussianShapeOperator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hI.apply b a]
  ring

theorem gaussianRicciDivergence_normal {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hT : ∀ a b : Fin 4, ricci (gaussianMetric h) z a.succ b.succ = 0) :
    nativeRicciDivergence (gaussianMetric h) z 0 =
      bulkPartial (gaussianResidualA h) 0 z + gaussianResidualDivergence h z +
        gaussianKappa h z * gaussianResidualA h z := by
  rw [gaussianRicciDivergence_split hN.self_of_nhds,
    gaussianCovariantRicci_rrr hh hN.self_of_nhds]
  simp_rw [gaussianCovariantRicci_abr hh hS hN hT]
  simp only [mul_add, Finset.sum_add_distrib]
  have ht :
      (∑ a : Fin 4, ∑ b : Fin 4,
        (h z)⁻¹ a b * (gaussianSecondForm h z a b * gaussianResidualA h z)) =
      gaussianKappa h z * gaussianResidualA h z := by
    rw [← gaussianSecondForm_trace_contraction hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [ht]
  rfl

theorem gaussianRicciDivergence_tangential {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hT : ∀ᶠ y in 𝓝 z, ∀ a b : Fin 4,
      ricci (gaussianMetric h) y a.succ b.succ = 0) (i : Fin 4) :
    nativeRicciDivergence (gaussianMetric h) z i.succ =
      bulkPartial (fun y => gaussianResidualC h y i) 0 z +
        gaussianKappa h z * gaussianResidualC h z i := by
  rw [gaussianRicciDivergence_split hN.self_of_nhds,
    gaussianCovariantRicci_rra hh hN.self_of_nhds]
  simp_rw [gaussianCovariantRicci_abi hh hS hN hT]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [gaussianShape_contraction hS.self_of_nhds i]
  have ht :
      (∑ a : Fin 4, ∑ b : Fin 4,
        (h z)⁻¹ a b * (gaussianSecondForm h z a b * gaussianResidualC h z i)) =
      gaussianKappa h z * gaussianResidualC h z i := by
    rw [← gaussianSecondForm_trace_contraction hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [ht]
  ring

/-- The exact homogeneous constraint system, derived from the actual native
contracted Bianchi identity and the tangential vacuum equations. -/
theorem gaussian_constraint_evolution {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (hT : ∀ᶠ y in 𝓝 z, ∀ a b : Fin 4,
      ricci (gaussianMetric h) y a.succ b.succ = 0) :
    bulkPartial (gaussianResidualA h) 0 z =
        -2 * gaussianResidualDivergence h z - 2 * gaussianKappa h z * gaussianResidualA h z ∧
      ∀ i : Fin 4, bulkPartial (fun y => gaussianResidualC h y i) 0 z =
        (1 / 2 : ℝ) * bulkPartial (gaussianResidualA h) i.succ z -
          gaussianKappa h z * gaussianResidualC h z i := by
  have hg := analyticAt_gaussianBlockMetric hh
  have hs := hS.mono (fun y hy => gaussianBlockMetric_symmetric hy)
  have hn := hN.mono (fun y hy => gaussianBlockMetric_unit hy)
  constructor
  · have hb := native_contracted_bianchi hg hs hn 0
    change 2 * nativeRicciDivergence (gaussianMetric h) z 0 = _ at hb
    rw [gaussianRicciDivergence_normal hh hS hN hT.self_of_nhds,
      gaussian_scalarCurvature_derivative hN hT] at hb
    linarith
  · intro i
    have hb := native_contracted_bianchi hg hs hn i.succ
    change 2 * nativeRicciDivergence (gaussianMetric h) z i.succ = _ at hb
    rw [gaussianRicciDivergence_tangential hh hS hN hT,
      gaussian_scalarCurvature_derivative hN hT] at hb
    linarith

end
end NSEGR.NativeLiterature
