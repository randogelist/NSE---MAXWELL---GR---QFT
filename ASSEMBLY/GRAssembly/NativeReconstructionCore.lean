import GRAssembly.NativeConservation
import GRAssembly.AnalyticHodge

/-! Boundary-admissible Hodge decoding and the exact NSE residual. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

theorem boundaryAdmissible_velocity_analytic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryVelocity K z.1 z.2)
      (spacetimeSlab t0 δ) :=
  leray_joint_analytic_on_open_slab (boundaryRawVelocity K) isOpen_Ioo
    (boundaryAdmissible_raw_analytic hK)
    (fun t ht => boundaryAdmissible_raw_periodic hK ht)

theorem boundaryAdmissible_solenoidal {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : divergence (boundaryVelocity K t) x = 0 := by
  exact congrFun (divergence_leray_zero _ (boundaryAdmissible_raw_smooth hK ht)
    (boundaryAdmissible_raw_periodic hK ht)) x

theorem boundaryAdmissible_potential_eq {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    boundaryPotential K t = poissonInverse (fun x => boundaryBeta K t x - ρ) := by
  simp only [boundaryPotential, boundaryAdmissible_beta_mean hK ht]

theorem boundaryAdmissible_potential_eq_eventually {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    boundaryPotential K =ᶠ[𝓝 t]
      (fun s => poissonInverse (fun x => boundaryBeta K s x - ρ)) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact boundaryAdmissible_potential_eq hK hs

theorem boundaryAdmissible_potential_analytic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryPotential K z.1 z.2)
      (spacetimeSlab t0 δ) := by
  have hinput : AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => boundaryBeta K z.1 z.2 - ρ) (spacetimeSlab t0 δ) :=
    fun z hz => (boundaryAdmissible_beta_analytic hK z hz).sub analyticAt_const
  have hper (t : ℝ) (ht : t ∈ timeInterval t0 δ) :
      SpatialPeriodic (fun x => boundaryBeta K t x - ρ) := by
    intro x i
    exact congrArg (fun q : ℝ => q - ρ) (boundaryAdmissible_beta_periodic hK ht x i)
  have ha := poissonInverse_joint_analytic_on_open_slab
    (fun t x => boundaryBeta K t x - ρ) isOpen_Ioo hinput hper
  intro z hz
  apply (ha z hz).congr
  have ht := (continuous_fst.continuousAt (x := z)).tendsto.eventually
    (isOpen_Ioo.mem_nhds hz)
  filter_upwards [ht] with y hy
  exact congrFun (boundaryAdmissible_potential_eq hK hy).symm y.2

theorem boundaryAdmissible_potential_laplacian {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : scalarLaplacian (boundaryPotential K t) x = boundaryBeta K t x - ρ := by
  have hb := analyticOnNhd_slab_slice_smooth (boundaryAdmissible_beta_analytic hK) ht
  have hp : SpatialPeriodic (fun y => boundaryBeta K t y - ρ) := by
    intro y i
    exact congrArg (fun q : ℝ => q - ρ) (boundaryAdmissible_beta_periodic hK ht y i)
  rw [boundaryAdmissible_potential_eq hK ht]
  have h := congrFun (scalarLaplacian_poissonInverse
    (fun y => boundaryBeta K t y - ρ) (hb.sub contDiff_const) hp) x
  rw [scalarMean_sub_const_native _ hb.continuous,
    boundaryAdmissible_beta_mean hK ht, sub_self] at h
  simpa only [Pi.sub_apply, sub_zero] using h

theorem boundaryAdmissible_potential_time {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    scalarLocalTimeDerivative (boundaryPotential K) t =
      poissonInverse (scalarLocalTimeDerivative (boundaryBeta K) t) := by
  have ha : AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryBeta K z.1 z.2 - ρ)
      (spacetimeSlab t0 δ) :=
    fun z hz => (boundaryAdmissible_beta_analytic hK z hz).sub analyticAt_const
  have hp (s : ℝ) (hs : s ∈ timeInterval t0 δ) :
      SpatialPeriodic (fun x => boundaryBeta K s x - ρ) := by
    intro y i
    exact congrArg (fun q : ℝ => q - ρ) (boundaryAdmissible_beta_periodic hK hs y i)
  have hd := poissonInverse_localTimeDerivative (fun s y => boundaryBeta K s y - ρ)
    isOpen_Ioo (analyticOnNhd_slab_contDiffOn ha) hp ht
  have heq : scalarLocalTimeDerivative (fun s y => boundaryBeta K s y - ρ) t =
      scalarLocalTimeDerivative (boundaryBeta K) t := by
    funext y
    exact deriv_sub_const ρ
  rw [heq] at hd
  rw [← hd]
  funext y
  have he : (fun s => boundaryPotential K s y) =ᶠ[𝓝 t]
      (fun s => poissonInverse (fun x => boundaryBeta K s x - ρ) y) :=
    (boundaryAdmissible_potential_eq_eventually hK ht).mono (fun s hs => congrFun hs y)
  exact he.deriv_eq

theorem boundaryAdmissible_potential_initial {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) : ∀ x, boundaryPotential K t0 x = 0 := by
  intro x
  have ht : t0 ∈ timeInterval t0 δ := by constructor <;> linarith [hK.radius_pos]
  rw [boundaryAdmissible_potential_eq hK ht]
  have heq : (fun y => boundaryBeta K t0 y - ρ) = (0 : ScalarField) := by
    funext y
    simp only [hK.beta_initial y, sub_self, Pi.zero_apply]
  simp only [heq, poissonInverse_zero_native, Pi.zero_apply]

theorem boundaryAdmissible_potential_time_initial {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    ∀ x, scalarLocalTimeDerivative (boundaryPotential K) t0 x = 0 := by
  intro x
  have ht : t0 ∈ timeInterval t0 δ := by constructor <;> linarith [hK.radius_pos]
  rw [boundaryAdmissible_potential_time hK ht]
  have heq : scalarLocalTimeDerivative (boundaryBeta K) t0 = (0 : ScalarField) :=
    funext hK.beta_time_initial
  simp only [heq, poissonInverse_zero_native, Pi.zero_apply]

theorem boundaryAdmissible_raw_recovery {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : boundaryRawVelocity K t x = boundaryVelocity K t x -
      gradient (scalarLocalTimeDerivative (boundaryPotential K) t) x := by
  have hdt : scalarLocalTimeDerivative (boundaryBeta K) t =
      -divergence (boundaryRawVelocity K t) :=
    funext (boundaryAdmissible_beta_time hK ht)
  rw [boundaryAdmissible_potential_time hK ht, hdt, poissonInverse_neg_native]
  apply PiLp.ext
  intro i
  simp only [boundaryVelocity, leray, PiLp.sub_apply, gradient, PiLp.toLp_apply,
    Pi.neg_apply, fderiv_neg, ContinuousLinearMap.neg_apply]
  ring

theorem boundaryAdmissible_hodge_time {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : localTimeDerivative (boundaryVelocity K) t x =
      localTimeDerivative (boundaryRawVelocity K) t x +
        gradient (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x := by
  have hq := boundaryAdmissible_potential_analytic hK (t, x) ht
  have hqt : AnalyticAt ℝ (fun z : ℝ × Vec =>
      scalarLocalTimeDerivative (boundaryPotential K) z.1 z.2) (t,x) :=
    analyticAt_jointTime hq
  have hgrad := analyticAt_gradient_joint hqt
  have hw := boundaryAdmissible_raw_analytic hK (t, x) ht
  have he : (fun s => boundaryVelocity K s x) =ᶠ[𝓝 t]
      (fun s => boundaryRawVelocity K s x +
        gradient (scalarLocalTimeDerivative (boundaryPotential K) s) x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hr := boundaryAdmissible_raw_recovery hK hs x
    exact (eq_sub_iff_add_eq.mp hr).symm
  change deriv (fun s => boundaryVelocity K s x) t = _
  rw [he.deriv_eq, deriv_fun_add hw.curry_left.differentiableAt
    hgrad.curry_left.differentiableAt]
  change localTimeDerivative (boundaryRawVelocity K) t x +
    localTimeDerivative (fun s => gradient (scalarLocalTimeDerivative (boundaryPotential K) s)) t x = _
  rw [scalar_time_gradient_commute hqt]

theorem scalarLocalTimeDerivative_periodic_native (ψ : Pressure)
    (hp : ∀ t, SpatialPeriodic (ψ t)) (t : ℝ) :
    SpatialPeriodic (scalarLocalTimeDerivative ψ t) := by
  intro x i
  have he : (fun s => ψ s (x + unitVector i)) = fun s => ψ s x :=
    funext (fun s => hp s x i)
  exact congrArg (fun f : ℝ → ℝ => deriv f t) he

theorem boundaryAdmissible_pressure_analytic {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryPressure ρ K z.1 z.2)
      (spacetimeSlab t0 δ) := by
  intro z hz
  have hk := boundaryAdmissible_entry_analytic hK 0 0 z hz
  have hu := boundaryAdmissible_velocity_analytic hK z hz
  have hq := boundaryAdmissible_potential_analytic hK z hz
  have hs : AnalyticAt ℝ (fun y : ℝ × Vec =>
      vectorSq3 (fun i => boundaryVelocity K y.1 y.2 i)) z := by
    apply analyticAt_vectorSq3_components
    intro i
    exact ((EuclideanSpace.proj i).analyticAt _).comp hu
  have hqtt : AnalyticAt ℝ (fun y : ℝ × Vec =>
      scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) y.1 y.2) z :=
    analyticAt_jointTime (analyticAt_jointTime hq)
  have hc : AnalyticAt ℝ (fun _ : ℝ × Vec => 2 * ρ) z := analyticAt_const
  have hi : AnalyticAt ℝ (fun _ : ℝ × Vec => (3 : ℝ)⁻¹) z := analyticAt_const
  simpa only [boundaryPressure, div_eq_mul_inv, Pi.neg_def, Pi.sub_def,
    Pi.add_def, Pi.mul_def] using
    (hk.neg.sub ((hc.add hs).mul hi)).sub hqtt

theorem boundaryAdmissible_decoded_pair {ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) :
    AnalyticPeriodicPair t0 δ (boundaryVelocity K) (boundaryPressure ρ K) where
  radius_pos := hK.radius_pos
  velocity_analytic := boundaryAdmissible_velocity_analytic hK
  pressure_analytic := boundaryAdmissible_pressure_analytic hK
  periodic_velocity := fun t ht => leray_periodic (boundaryAdmissible_raw_periodic hK ht)
  periodic_pressure := by
    intro t ht x i
    have hu : boundaryVelocity K t (x + unitVector i) = boundaryVelocity K t x :=
      leray_periodic (boundaryAdmissible_raw_periodic hK ht) x i
    have hq : ∀ s, SpatialPeriodic (boundaryPotential K s) :=
      fun s => poissonInverse_periodic _
    have htt := scalarLocalTimeDerivative_periodic_native _
      (scalarLocalTimeDerivative_periodic_native _ hq) t x i
    simp only [boundaryPressure, hK.periodic t ht x i, hu, htt]

theorem boundaryAdmissible_residual {ν ρ t0 δ : ℝ} {K : BoundaryTensor}
    (hK : BoundaryAdmissible ρ t0 δ K) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) : nseResidual ν (boundaryVelocity K) (boundaryPressure ρ K) t x =
      tensorDivergence (boundaryStress ν K t) x := by
  have hu := analyticOnNhd_slab_slice_smooth (boundaryAdmissible_velocity_analytic hK) ht
  have hq := analyticOnNhd_slab_slice_smooth (boundaryAdmissible_potential_analytic hK) ht
  have hentry (a b : Fin 4) : DifferentiableAt ℝ (fun y => K t y a b) x :=
    ((boundaryAdmissible_entry_analytic hK a b (t, x) ht).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hqtt : DifferentiableAt ℝ
      (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x :=
    ((analyticAt_jointTime (analyticAt_jointTime
      (boundaryAdmissible_potential_analytic hK (t, x) ht))).comp
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  exact reconstruction_residual_of_codazzi_hodge ν ρ K t x
    (fun i j => hentry i.succ j.succ) hu hq
    (funext (boundaryAdmissible_solenoidal hK ht))
    (boundaryAdmissible_potential_laplacian hK ht) (hentry 0 0) hqtt
    (boundaryAdmissible_rawVelocity_time hK ht x) (boundaryAdmissible_hodge_time hK ht x)


end
end NSEGR.Assembly
