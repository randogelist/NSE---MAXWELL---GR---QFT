import GRAssembly.NativeGaussianEvolutionJet

/-! The actual tangential Ricci equation is the rational Gaussian acceleration equation. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem gaussianExtrinsicRicci_algebra (H K : Tensor4)
    (hH : H.IsSymm) (hK : K.IsSymm) (a b : Fin 4) :
    (∑ d : Fin 4, K b d * (H * K) d a) +
      (∑ c : Fin 4, -((H * K) c c * K a b) + (H * K) c b * K a c) =
      -(Matrix.trace (H * K) * K a b) + 2 * (K * H * K) a b := by
  have hQ : (K * H * K).IsSymm := by
    change (K * H * K).transpose = K * H * K
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hK.eq, hH.eq]
    exact (Matrix.mul_assoc K H K).symm
  have hfirst : (∑ d : Fin 4, K b d * (H * K) d a) = (K * H * K) a b := by
    change (K * (H * K)) b a = _
    rw [← Matrix.mul_assoc]
    exact hQ.apply a b
  have hsecond : (∑ c : Fin 4, (H * K) c b * K a c) = (K * H * K) a b := by
    rw [Matrix.mul_assoc]
    change (∑ c : Fin 4, (H * K) c b * K a c) = ∑ c : Fin 4, K a c * (H * K) c b
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have htrace : (∑ c : Fin 4, -((H * K) c c * K a b)) =
      -(Matrix.trace (H * K) * K a b) := by
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    rfl
  rw [Finset.sum_add_distrib, hfirst, hsecond, htrace]
  ring

theorem gaussianSecondForm_eq_half_radial {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) :
    gaussianSecondForm h z = (1 / 2 : ℝ) • coordDeriv h 0 z := by
  ext a b
  simp only [gaussianSecondForm, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul,
    coordDeriv_tensor_entry hh]

theorem gaussianSecondForm_radial {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (a b : Fin 4) :
    bulkPartial (fun y => gaussianSecondForm h y a b) 0 z =
      (1 / 2 : ℝ) * coordDeriv (coordDeriv h 0) 0 z a b := by
  rw [coordDeriv_tensor_second_entry hh]
  unfold gaussianSecondForm
  rw [Assembly.bulkPartial_mul analyticAt_const
    (Assembly.analyticAt_bulkPartial (Assembly.analyticAt_matrix_entry hh a b) 0)]
  simp

theorem gaussianShapeOperator_eq_mul (h : Bulk → Tensor4) (z : Bulk) :
    gaussianShapeOperator h z = (h z)⁻¹ * gaussianSecondForm h z := rfl

theorem coordDeriv_tensor_symmetric {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm) (i : Fin 5) :
    (coordDeriv h i z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  rw [coordDeriv_tensor_entry hh, coordDeriv_tensor_entry hh]
  apply Assembly.bulkPartial_congr_of_eventuallyEq
  exact hS.mono (fun y hy => hy.apply a b)

theorem coordDeriv_tensor_second_symmetric {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm) (i j : Fin 5) :
    (coordDeriv (coordDeriv h i) j z).IsSymm := by
  apply coordDeriv_tensor_symmetric (analyticAt_coordDeriv hh i)
  filter_upwards [hh.eventually_analyticAt, eventually_eventually_nhds.2 hS] with y hy hs
  exact coordDeriv_tensor_symmetric hy hs i

def gaussianTangentialNativeRicci (h : Bulk → Tensor4) (z : Bulk) : Tensor4 :=
  fun a b => ricci (gaussianMetric h) z a.succ b.succ

private theorem jet_analyticAt_gaussianMetric {h : Bulk → Tensor4} {z : Bulk}
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

theorem gaussianTangentialNativeRicci_symmetric {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) :
    (gaussianTangentialNativeRicci h z).IsSymm := by
  have hgs : ∀ᶠ y in 𝓝 z, (gaussianMetric h y).IsSymm := by
    filter_upwards [hS] with y hy
    change (gaussianMatrix (h y)).transpose = gaussianMatrix (h y)
    rw [← gaussianMatrix_transpose, hy.eq]
  have hgn : ∀ᶠ y in 𝓝 z, IsUnit (gaussianMetric h y).det := by
    filter_upwards [hN] with y hy
    exact gaussianMatrix_isUnit_det (h y) hy
  have hr := nativeRicci_symmetric (jet_analyticAt_gaussianMetric hh) hgs hgn
  apply Matrix.IsSymm.ext
  intro a b
  exact hr.apply a.succ b.succ

theorem gaussianTangentialRicci_eq_intrinsic_extrinsic {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (a b : Fin 4) :
    gaussianTangentialNativeRicci h z a b =
      -(1 / 2 : ℝ) * coordDeriv (coordDeriv h 0) 0 z a b +
      gaussianIntrinsicRicci h z a b -
      Matrix.trace ((h z)⁻¹ * gaussianSecondForm h z) * gaussianSecondForm h z a b +
      2 * (gaussianSecondForm h z * (h z)⁻¹ * gaussianSecondForm h z) a b := by
  have hi : ((h z)⁻¹).IsSymm := by
    change ((h z)⁻¹).transpose = (h z)⁻¹
    rw [Matrix.transpose_nonsing_inv, hS.self_of_nhds.eq]
  have hk : (gaussianSecondForm h z).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    unfold gaussianSecondForm
    congr 1
    apply Assembly.bulkPartial_congr_of_eventuallyEq
    exact hS.mono (fun y hy => hy.apply a b)
  have hex := gaussianExtrinsicRicci_algebra (h z)⁻¹ (gaussianSecondForm h z) hi hk a b
  change ricci (gaussianMetric h) z a.succ b.succ = _
  rw [Assembly.ricci_gaussian_tangential h z hN]
  unfold Assembly.gaussianTangentialRicciComponent gaussianIntrinsicRicci
  rw [gaussianSecondForm_radial hh]
  simp only [gaussianShapeOperator_eq_mul] at hex ⊢
  simp only [Finset.sum_add_distrib] at hex ⊢
  linear_combination hex

theorem gaussianJet_rawAcceleration_eq_native {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (hC : GaussianJetCompatible h z J) :
    2 • gaussianJetRicci J - gaussianJetTrace J • gaussianJetVelocity J +
      gaussianJetVelocity J * (gaussianJetMetric J)⁻¹ * gaussianJetVelocity J =
      coordDeriv (coordDeriv h 0) 0 z + 2 • gaussianTangentialNativeRicci h z := by
  ext a b
  have hr := gaussianTangentialRicci_eq_intrinsic_extrinsic hh hS hN a b
  simp only [gaussianSecondForm_eq_half_radial hh,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at hr
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul,
    gaussianJetRicci_eq_native hh hN.self_of_nhds hC,
    gaussianJetTrace, hC.metric, hC.velocity]
  linear_combination -2 * hr

theorem gaussianCKRHS_velocity_eq_native {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (hC : GaussianJetCompatible h z J) :
    gaussianStateVelocity (gaussianCKRHS J) =
      coordDeriv (coordDeriv h 0) 0 z + 2 • gaussianTangentialNativeRicci h z := by
  change gaussianSymmetrize _ = _
  rw [gaussianJet_rawAcceleration_eq_native hh hS hN hC]
  apply gaussianSymmetrize_eq_of_isSymm
  apply Matrix.IsSymm.ext
  intro a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul,
    (coordDeriv_tensor_second_symmetric hh hS 0 0).apply a b,
    (gaussianTangentialNativeRicci_symmetric hh hS hN).apply a b]

theorem gaussianTangentialVacuum_iff_CKRHS {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hS : ∀ᶠ y in 𝓝 z, (h y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (hC : GaussianJetCompatible h z J) :
    (∀ a b : Fin 4, ricci (gaussianMetric h) z a.succ b.succ = 0) ↔
      coordDeriv (coordDeriv h 0) 0 z = gaussianStateVelocity (gaussianCKRHS J) := by
  rw [gaussianCKRHS_velocity_eq_native hh hS hN hC]
  constructor
  · intro hv
    have ht : gaussianTangentialNativeRicci h z = 0 := by
      ext a b
      exact hv a b
    rw [ht, smul_zero, add_zero]
  · intro he a b
    have hab := congrArg (fun A : Tensor4 => A a b) he
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul,
      gaussianTangentialNativeRicci] at hab
    linarith

end
end NSEGR.NativeLiterature
