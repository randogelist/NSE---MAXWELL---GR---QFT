import GRAssembly.NativeCalculus
import GRAdapter.Contracts

/-! Native Codazzi time component and conserved boundary mean. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
namespace NSEGR.Assembly
noncomputable section

theorem boundaryAdmissible_entry_analytic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) (a b : Fin 4) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => K z.1 z.2 a b) (spacetimeSlab t0 δ) :=
  fun z hz => analyticAt_tensor4_entry (hK.analytic z hz) a b

theorem boundaryAdmissible_beta_analytic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryBeta K z.1 z.2) (spacetimeSlab t0 δ) :=
  fun z hz => analyticAt_boundaryBeta (hK.analytic z hz)

theorem boundaryAdmissible_raw_analytic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryRawVelocity K z.1 z.2)
      (spacetimeSlab t0 δ) :=
  fun z hz => analyticAt_boundaryRawVelocity (hK.analytic z hz)

theorem boundaryAdmissible_beta_periodic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    SpatialPeriodic (boundaryBeta K t) := by
  intro x i
  simp only [boundaryBeta, hK.periodic t ht x i]

theorem boundaryAdmissible_raw_periodic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    SpatialPeriodic (boundaryRawVelocity K t) := by
  intro x i
  simp only [boundaryRawVelocity, hK.periodic t ht x i]

theorem boundaryAdmissible_raw_smooth {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    ContDiff ℝ ∞ (boundaryRawVelocity K t) :=
  analyticOnNhd_slab_slice_smooth (boundaryAdmissible_raw_analytic hK) ht

theorem boundaryAdmissible_beta_time {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : scalarLocalTimeDerivative (boundaryBeta K) t x =
      -divergence (boundaryRawVelocity K t) x := by
  have hdiag : (fun s y => K s y 0 0 - lorentzTrace4 (K s y) * eta4 0 0) =
      fun s y => -boundaryBeta K s y := by
    funext s y
    simp [lorentzTrace4, eta4, lorentzSign4, boundaryBeta, spatialIndex4,
      Fin.sum_univ_succ]
    <;> ring
  have hmix (i : Fin 3) :
      (fun y => K t y i.succ 0 - lorentzTrace4 (K t y) * eta4 i.succ 0) =
        fun y => K t y i.succ 0 := by
    funext y
    simp [eta4, Fin.succ_ne_zero]
  have hs (i : Fin 3) : (fun y => K t y i.succ 0) =
      fun y => K t y 0 i.succ := by
    funext y
    exact (hK.symmetric t ht y).apply 0 i.succ
  have hd (i : Fin 3) :
      fderiv ℝ (fun y => K t y 0 i.succ) x (unitVector i) =
        spatialPartial (boundaryRawVelocity K t) i x i := by
    exact StressCalc.component_fderiv
      ((boundaryAdmissible_raw_smooth hK ht).differentiable (by simp) x) _ i
  have hc := hK.momentum_constraint t ht x 0
  rw [boundaryCodazzi, Fin.sum_univ_succ, hdiag] at hc
  have hneg : deriv (fun s => -boundaryBeta K s x) t =
      -deriv (fun s => boundaryBeta K s x) t := deriv.neg
  simp only [boundaryPartial, Fin.cases_zero, Fin.cases_succ,
    lorentzSign4, Fin.succ_ne_zero, ite_true, ite_false, one_mul,
    hmix, hneg, neg_one_mul, neg_neg, hs, hd] at hc
  change scalarLocalTimeDerivative (boundaryBeta K) t x +
    divergence (boundaryRawVelocity K t) x = 0 at hc
  linarith

theorem boundaryAdmissible_beta_mean {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    scalarMean (boundaryBeta K t) = ρ := by
  let m : ℝ → ℝ := fun s => scalarMean (boundaryBeta K s)
  have hm (s : ℝ) (hs : s ∈ timeInterval t0 δ) : HasDerivAt m 0 s := by
    have hd := scalarMean_hasDerivAt_local (boundaryBeta K) isOpen_Ioo
      (analyticOnNhd_slab_contDiffOn (boundaryAdmissible_beta_analytic hK))
      (fun v hv => boundaryAdmissible_beta_periodic hK hv) hs
    have heq : scalarLocalTimeDerivative (boundaryBeta K) s =
        -divergence (boundaryRawVelocity K s) := by
      funext y
      exact boundaryAdmissible_beta_time hK hs y
    rw [heq] at hd
    have hz : scalarMean (-divergence (boundaryRawVelocity K s)) = 0 := by
      change (∫ x in unitCube, -divergence (boundaryRawVelocity K s) x) = 0
      rw [integral_neg]
      change -scalarMean (divergence (boundaryRawVelocity K s)) = 0
      rw [scalarMean_divergence_zero (boundaryAdmissible_raw_smooth hK hs)
        (boundaryAdmissible_raw_periodic hK hs), neg_zero]
    rw [hz] at hd
    exact hd
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hm s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hm s hs).deriv) ht
    (show t0 ∈ timeInterval t0 δ by constructor <;> linarith [hK.radius_pos])
  change m t = ρ
  rw [hconst]
  have hinit : boundaryBeta K t0 = fun _ => ρ := funext hK.beta_initial
  change scalarMean (boundaryBeta K t0) = ρ
  rw [hinit, scalarMean_const]

theorem boundaryAdmissible_rawVelocity_time {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : localTimeDerivative (boundaryRawVelocity K) t x =
      tensorDivergence (boundarySpatialTensor K t) x +
        gradient (fun y => K t y 0 0) x + gradient (boundaryBeta K t) x := by
  let A := boundarySpatialTensor K t
  let f : ScalarField := fun y => K t y 0 0 + boundaryBeta K t y
  let J : TensorField := fun y i j => f y * identity3 i j
  let T : TensorField := fun y => A y + J y
  have hka : DifferentiableAt ℝ (fun y => K t y 0 0) x :=
    ((boundaryAdmissible_entry_analytic hK 0 0 (t, x) ht).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hba : DifferentiableAt ℝ (boundaryBeta K t) x :=
    ((boundaryAdmissible_beta_analytic hK (t, x) ht).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hfa : DifferentiableAt ℝ f x := hka.add hba
  have hAa (i j : Fin 3) : DifferentiableAt ℝ (fun y => A y i j) x :=
    ((boundaryAdmissible_entry_analytic hK i.succ j.succ (t, x) ht).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hJa (i j : Fin 3) : DifferentiableAt ℝ (fun y => J y i j) x :=
    hfa.mul_const _
  have hdiv : tensorDivergence T x = tensorDivergence A x + gradient f x := by
    rw [tensorDivergence_add A J x hAa hJa,
      tensorDivergence_isotropic f x hfa]
  have hg : gradient f x = gradient (fun y => K t y 0 0) x + gradient (boundaryBeta K t) x := by
    have hd : HasFDerivAt f (fderiv ℝ (fun y => K t y 0 0) x +
        fderiv ℝ (boundaryBeta K t) x) x := hka.hasFDerivAt.add hba.hasFDerivAt
    apply PiLp.ext
    intro i
    simpa only [gradient, PiLp.toLp_apply, PiLp.add_apply, ContinuousLinearMap.add_apply] using
      congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) hd.fderiv
  have hflux (i j : Fin 3) :
      (fun y => K t y i.succ j.succ - lorentzTrace4 (K t y) * eta4 i.succ j.succ) =
        fun y => T y j i := by
    funext y
    rw [reconstruction_eta4_spatial, reconstruction_lorentzTrace_boundary]
    change K t y i.succ j.succ - (-K t y 0 0 - boundaryBeta K t y) * identity3 i j =
      K t y j.succ i.succ + (K t y 0 0 + boundaryBeta K t y) * identity3 j i
    rw [(hK.symmetric t ht y).apply j.succ i.succ]
    simp only [identity3, eq_comm]
    ring
  have htime (j : Fin 3) :
      (fun s => K s x 0 j.succ - lorentzTrace4 (K s x) * eta4 0 j.succ) =
        fun s => boundaryRawVelocity K s x j := by
    funext s
    simp [eta4, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero j), boundaryRawVelocity,
      spatialIndex4]
  apply PiLp.ext
  intro j
  have hc := hK.momentum_constraint t ht x j.succ
  rw [boundaryCodazzi, Fin.sum_univ_succ] at hc
  simp only [boundaryPartial, Fin.cases_zero, Fin.cases_succ, lorentzSign4,
    Fin.succ_ne_zero, ite_true, ite_false, one_mul, neg_one_mul, htime, hflux] at hc
  rw [velocity_coordinate_timeDerivative
    (boundaryAdmissible_raw_analytic hK (t, x) ht) j] at hc
  change -localTimeDerivative (boundaryRawVelocity K) t x j + tensorDivergence T x j = 0 at hc
  rw [hdiv, hg] at hc
  simp only [PiLp.add_apply] at hc ⊢
  linarith

end
end NSEGR.Assembly
