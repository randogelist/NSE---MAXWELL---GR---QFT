import GRAssembly.NativeGaussianEvolution
import GRAssembly.NativeGaussianMetricCurvature
import GRAssembly.BoundaryConstraintsGeometry

/-! Compatibility of the finite CK jet with the actual Gaussian metric derivatives. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem coordDeriv_tensor_entry {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (i : Fin 5) (a b : Fin 4) :
    coordDeriv h i z a b = bulkPartial (fun y => h y a b) i z := by
  exact (Assembly.matrix_entry_fderiv hh.differentiableAt (bulkBasis i) a b).symm

theorem coordDeriv_tensor_second_entry {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (i j : Fin 5) (a b : Fin 4) :
    coordDeriv (coordDeriv h j) i z a b =
      bulkPartial (fun y => bulkPartial (fun q => h q a b) j y) i z := by
  rw [coordDeriv_tensor_entry (analyticAt_coordDeriv hh j)]
  apply Assembly.bulkPartial_congr_of_eventuallyEq
  filter_upwards [hh.eventually_analyticAt] with y hy
  exact coordDeriv_tensor_entry hy j a b

theorem coordDeriv_tensorInverse {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hN : IsUnit (h z).det) (i : Fin 5) :
    coordDeriv (fun y => (h y)⁻¹) i z =
      -((h z)⁻¹ * coordDeriv h i z * (h z)⁻¹) := by
  have hu : IsUnit (h z) := (h z).isUnit_iff_isUnit_det.mpr hN
  have hi : HasFDerivAt (fun H : Tensor4 => H⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Tensor4 (h z)⁻¹ (h z)⁻¹) (h z) := by
    have he : (fun H : Tensor4 => H⁻¹) = Ring.inverse := by
      funext H
      exact Matrix.nonsing_inv_eq_ringInverse H
    rw [he]
    simpa only [Matrix.coe_units_inv, IsUnit.unit_spec]
      using (hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit)
  have hd := hi.comp z hh.differentiableAt.hasFDerivAt
  unfold coordDeriv
  have hd' : fderiv ℝ (fun y => (h y)⁻¹) z =
      (-ContinuousLinearMap.mulLeftRight ℝ Tensor4 (h z)⁻¹ (h z)⁻¹).comp
        (fderiv ℝ h z) := by
    simpa only [Function.comp_def] using hd.fderiv
  rw [hd']
  rfl

structure GaussianJetCompatible (h : Bulk → Tensor4) (z : Bulk)
    (J : CKJet GaussianBase GaussianState) : Prop where
  metric : gaussianJetMetric J = h z
  velocity : gaussianJetVelocity J = coordDeriv h 0 z
  spatial : ∀ a, gaussianJetSpatial J a = coordDeriv h a.succ z
  second : ∀ a b, gaussianJetSecond J a b =
    coordDeriv (coordDeriv h b.succ) a.succ z

theorem gaussianJetConnection_eq_native {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hC : GaussianJetCompatible h z J) (a b c : Fin 4) :
    gaussianJetConnection J a b c = gaussianTangentialChristoffel h z a b c := by
  simp only [gaussianJetConnection, hC.metric, hC.spatial,
    coordDeriv_tensor_entry hh, gaussianTangentialChristoffel]

theorem gaussianJetInverseDerivative_eq_native {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hN : IsUnit (h z).det) (hC : GaussianJetCompatible h z J) (c : Fin 4) :
    gaussianJetInverseDerivative J c = coordDeriv (fun y => (h y)⁻¹) c.succ z := by
  rw [coordDeriv_tensorInverse hh hN]
  simp only [gaussianJetInverseDerivative, hC.metric, hC.spatial]

private theorem jet_bulkPartial_const_mul {f : Bulk → ℝ} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (r : ℝ) (i : Fin 5) :
    bulkPartial (fun y => r * f y) i z = r * bulkPartial f i z := by
  rw [Assembly.bulkPartial_mul analyticAt_const hf]
  simp

private theorem jet_bulkPartial_add {f g : Bulk → ℝ} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) (i : Fin 5) :
    bulkPartial (fun y => f y + g y) i z = bulkPartial f i z + bulkPartial g i z :=
  coordDeriv_add hf hg i

private theorem jet_bulkPartial_sub {f g : Bulk → ℝ} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) (i : Fin 5) :
    bulkPartial (fun y => f y - g y) i z = bulkPartial f i z - bulkPartial g i z :=
  coordDeriv_sub hf hg i

theorem gaussianJetConnectionDerivative_eq_native {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hN : IsUnit (h z).det) (hC : GaussianJetCompatible h z J)
    (c a b d : Fin 4) :
    gaussianJetConnectionDerivative J c a b d =
      bulkPartial (fun y => gaussianTangentialChristoffel h y a b d) c.succ z := by
  have hi := Assembly.analyticAt_matrix_inverse hh hN
  have hp (i a b : Fin 4) :
      AnalyticAt ℝ (fun y => bulkPartial (fun q => h q a b) i.succ y) z :=
    Assembly.analyticAt_bulkPartial (Assembly.analyticAt_matrix_entry hh a b) i.succ
  have hs (e : Fin 4) := ((hp b e d).add (hp d e b)).sub (hp e b d)
  have hprod (e : Fin 4) := (Assembly.analyticAt_matrix_entry hi a e).mul (hs e)
  symm
  unfold gaussianTangentialChristoffel
  rw [jet_bulkPartial_const_mul (Finset.analyticAt_fun_sum Finset.univ (fun e _ => hprod e))]
  rw [Assembly.bulkPartial_sum hprod]
  unfold gaussianJetConnectionDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [Assembly.bulkPartial_mul (Assembly.analyticAt_matrix_entry hi a e) (hs e),
    jet_bulkPartial_sub ((hp b e d).add (hp d e b)) (hp e b d),
    jet_bulkPartial_add (hp b e d) (hp d e b)]
  rw [gaussianJetInverseDerivative_eq_native hh hN hC]
  simp only [hC.metric, hC.spatial, hC.second,
    coordDeriv_tensor_entry hh, coordDeriv_tensor_entry hi,
    coordDeriv_tensor_second_entry hh]

def gaussianIntrinsicRicci (h : Bulk → Tensor4) (z : Bulk) : Tensor4 := fun a b =>
  (∑ c : Fin 4,
    bulkPartial (fun y => gaussianTangentialChristoffel h y c a b) c.succ z -
      bulkPartial (fun y => gaussianTangentialChristoffel h y c a c) b.succ z) +
  ∑ c : Fin 4, ∑ d : Fin 4,
    gaussianTangentialChristoffel h z c c d * gaussianTangentialChristoffel h z d a b -
      gaussianTangentialChristoffel h z c b d * gaussianTangentialChristoffel h z d a c

theorem gaussianJetRicci_eq_native {h : Bulk → Tensor4} {z : Bulk}
    {J : CKJet GaussianBase GaussianState} (hh : AnalyticAt ℝ h z)
    (hN : IsUnit (h z).det) (hC : GaussianJetCompatible h z J) :
    gaussianJetRicci J = gaussianIntrinsicRicci h z := by
  ext a b
  simp only [gaussianJetRicci, gaussianIntrinsicRicci,
    gaussianJetConnection_eq_native hh hC,
    gaussianJetConnectionDerivative_eq_native hh hN hC]

end
end NSEGR.NativeLiterature
