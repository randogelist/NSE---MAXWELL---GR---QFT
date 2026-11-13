import GRAssembly.NativeReconstructionCore
import GRAssembly.NativeCompletionCalculus
import GRAssembly.NativeGluingScalar
import GRAssembly.PressureGauge

/-! Actual conserved scalar completion and the complete boundary witness. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

theorem poissonInverse_sub_native (f g : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hp : SpatialPeriodic f) (hq : SpatialPeriodic g) :
    poissonInverse (f-g) = poissonInverse f - poissonInverse g := by
  simp only [poissonInverse_eq_neg_scalarL,
    NSEMaxwell.HodgeProof.scalarL_sub f g hf hg hp hq]
  funext x
  simp only [Pi.neg_apply, Pi.sub_apply]
  ring

theorem leray_sub_native (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hp : SpatialPeriodic a) (hq : SpatialPeriodic b) : leray (a-b) = leray a - leray b := by
  have hDa := divergence_smooth a ha
  have hDb := divergence_smooth b hb
  have hGa := poissonInverse_smooth _ hDa (divergence_periodic hp)
  have hGb := poissonInverse_smooth _ hDb (divergence_periodic hq)
  unfold leray
  rw [divergence_sub a b ha hb, poissonInverse_sub_native _ _ hDa hDb
    (divergence_periodic hp) (divergence_periodic hq)]
  funext x
  apply PiLp.ext
  intro i
  simp only [Pi.sub_apply, PiLp.sub_apply, gradient, PiLp.toLp_apply]
  rw [fderiv_sub (hGa.differentiable (by simp) x) (hGb.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem completedBoundary_velocity_recovery {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure}
    (hn : LocalNSE ν t0 δ u p)
    (hψ : AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 δ))
    (hper : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (ψ t))
    {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    boundaryVelocity (completedBoundary ν ρ u p ψ) t = u t := by
  have hu := analyticOnNhd_slab_slice_smooth hn.velocity_analytic ht
  have hqt : ContDiff ℝ ∞ (scalarLocalTimeDerivative ψ t) :=
    analyticOnNhd_slab_slice_smooth (fun z hz => analyticAt_jointTime (hψ z hz)) ht
  have hqtp := scalarLocalTimeDerivative_periodic_on_interval isOpen_Ioo hper ht
  change leray (boundaryRawVelocity (completedBoundary ν ρ u p ψ) t) = u t
  rw [completedBoundary_rawVelocity]
  change leray (u t - gradient (scalarLocalTimeDerivative ψ t)) = u t
  rw [leray_sub_native _ _ hu (gradient_smooth hqt) (hn.periodic_velocity t ht)
    (gradient_periodic hqtp), leray_eq_self_of_divergence_zero _
      (funext (hn.divergence_free t ht)), leray_gradient_zero _ hqt hqtp, sub_zero]

theorem completedBoundary_potential_recovery {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure}
    (hn : LocalNSE ν t0 δ u p)
    (hψ : AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 δ))
    (hper : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (ψ t))
    (hK : BoundaryAdmissible ρ t0 δ (completedBoundary ν ρ u p ψ))
    {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    boundaryPotential (completedBoundary ν ρ u p ψ) t =
      fun x => ψ t x - scalarMean (ψ t) := by
  rw [boundaryAdmissible_potential_eq hK ht]
  have he : (fun x => boundaryBeta (completedBoundary ν ρ u p ψ) t x - ρ) =
      scalarLaplacian (ψ t) := by
    funext x
    change boundaryBeta (completedBoundary ν ρ u p ψ) t x - ρ = scalarLaplacian (ψ t) x
    rw [completedBoundary_beta ν ρ u p ψ t x (hn.divergence_free t ht x)]
    ring
  rw [he]
  exact poissonInverse_scalarLaplacian _ (analyticOnNhd_slab_slice_smooth hψ ht) (hper t ht)

theorem completedBoundary_stress_zero {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure}
    (hn : LocalNSE ν t0 δ u p)
    (hψ : AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 δ))
    (hper : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (ψ t))
    (hK : BoundaryAdmissible ρ t0 δ (completedBoundary ν ρ u p ψ))
    {t : ℝ} (ht : t ∈ timeInterval t0 δ) (x : Vec) :
    boundaryStress ν (completedBoundary ν ρ u p ψ) t x = 0 := by
  let K := completedBoundary ν ρ u p ψ
  have hv : boundaryVelocity K t = u t :=
    completedBoundary_velocity_recovery (ρ := ρ) hn hψ hper ht
  have hq := completedBoundary_potential_recovery hn hψ hper hK ht
  have hT : boundarySpatialTensor K t x + velocityOuter (boundaryVelocity K t x) +
      scalarHessian (boundaryPotential K t) x - ν • strain (boundaryVelocity K t) x =
        fun i j => ((vectorSq3 (fun l => u t x l) - ρ)/3) * identity3 i j := by
    rw [hv, hq, scalarHessian_sub_constant]
    ext i j
    change K t x i.succ j.succ + u t x i * u t x j +
      scalarHessian (ψ t) x i j - ν * strain (u t) x i j = _
    have hspace : K t x i.succ j.succ =
        ((vectorSq3 (fun l => u t x l) - ρ) / 3) * identity3 i j -
          u t x i * u t x j + ν * strain (u t) x i j - scalarHessian (ψ t) x i j :=
      completedBoundary_space_space ν ρ u p ψ t x (hn.divergence_free t ht x) i j
    have hstep := congrArg (fun k : ℝ => k + u t x i * u t x j +
      scalarHessian (ψ t) x i j - ν * strain (u t) x i j) hspace
    exact hstep.trans (by ring)
  change tf3 _ = 0
  rw [hT]
  apply (tf3_eq_zero_iff _).mpr
  intro i j
  simp only [trace3, identity3_diag, mul_one]
  ring

theorem completedBoundary_pressure_recovery {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure}
    (hn : LocalNSE ν t0 δ u p)
    (hψ : AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 δ))
    (hper : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (ψ t))
    (hK : BoundaryAdmissible ρ t0 δ (completedBoundary ν ρ u p ψ)) :
    SameFlowAt t0 (boundaryVelocity (completedBoundary ν ρ u p ψ))
      (boundaryPressure ρ (completedBoundary ν ρ u p ψ)) u p := by
  let K := completedBoundary ν ρ u p ψ
  let a : ℝ → ℝ := fun t => ψ t 0 - boundaryPotential K t 0
  have ha (t : ℝ) (ht : t ∈ timeInterval t0 δ) : AnalyticAt ℝ a t :=
    (hψ (t,0) ht).curry_left.sub (boundaryAdmissible_potential_analytic hK (t,0) ht).curry_left
  have haeq (t : ℝ) (ht : t ∈ timeInterval t0 δ) : a t = scalarMean (ψ t) := by
    dsimp [a]
    rw [completedBoundary_potential_recovery hn hψ hper hK ht]
    ring
  have hq (t : ℝ) (ht : t ∈ timeInterval t0 δ) :
      boundaryPotential K t = fun x => ψ t x - a t := by
    rw [haeq t ht]
    exact completedBoundary_potential_recovery hn hψ hper hK ht
  filter_upwards [timeInterval_mem_nhds t0 δ hn.radius_pos] with t ht
  refine ⟨completedBoundary_velocity_recovery hn hψ hper ht, deriv (deriv a) t, ?_⟩
  intro x
  have he : (fun s => boundaryPotential K s x) =ᶠ[𝓝 t] fun s => ψ s x - a s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact congrFun (hq s hs) x
  have hdd : scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t x =
      scalarLocalTimeDerivative (scalarLocalTimeDerivative (fun s y => ψ s y - a s)) t x :=
    he.deriv.deriv_eq
  rw [scalarSecondTimeDerivative_gauge (hψ (t,x) ht) (ha t ht)] at hdd
  change -K t x 0 0 - (2 * ρ + vectorSq3 (fun i => boundaryVelocity K t x i))/3 -
    scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t x =
      p t x + deriv (deriv a) t
  have h00 : K t x 0 0 =
      -(2 * ρ + vectorSq3 (fun i => u t x i)) / 3 - p t x -
        scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x :=
    completedBoundary_time_time ν ρ u p ψ t x (hn.divergence_free t ht x)
  have hv : boundaryVelocity K t = u t :=
    completedBoundary_velocity_recovery (ρ := ρ) hn hψ hper ht
  have hs := congrArg (fun v : Field => vectorSq3 (fun i => v x i)) hv
  have hkin := congrArg₂ (fun k s : ℝ => -k - (2 * ρ + s) / 3) h00 hs
  have hwhole := congrArg₂ (fun s q : ℝ => s - q) hkin hdd
  exact hwhole.trans (by ring)

theorem localNSE_restrict_native {ν t0 δ d : ℝ} {u : Velocity} {p : Pressure}
    (hn : LocalNSE ν t0 δ u p) (hd : 0 < d) (hle : d ≤ δ) : LocalNSE ν t0 d u p where
  radius_pos := hd
  velocity_analytic := fun z hz => hn.velocity_analytic z (timeInterval_mono hle hz)
  pressure_analytic := fun z hz => hn.pressure_analytic z (timeInterval_mono hle hz)
  periodic_velocity := fun t ht => hn.periodic_velocity t (timeInterval_mono hle ht)
  periodic_pressure := fun t ht => hn.periodic_pressure t (timeInterval_mono hle ht)
  divergence_free := fun t ht => hn.divergence_free t (timeInterval_mono hle ht)
  momentum := fun t ht => hn.momentum t (timeInterval_mono hle ht)

theorem scalarBoundaryCompletionLaws_of_literatureCK
    (input : LiteratureAnalyticCKInput) (ν ρ t0 : ℝ) (hρ : ρ ≠ 0) :
    ScalarBoundaryCompletionLaws ν ρ t0 where
  complete := by
    intro n
    obtain ⟨d, ψ, hd, hle, hψ, hper, h0, h1, hH⟩ :=
      scalar_periodic_cylinder_of_literatureCK (ν := ν) input hρ n.solution.toAnalyticPeriodicPair
    have hn := localNSE_restrict_native n.solution hd hle
    have hK := completedBoundary_admissible hn hψ hper h0 h1 hH
    exact ⟨{
      timeRadius := d
      radius_le_source := hle
      potential := ψ
      potential_analytic := hψ
      potential_periodic := hper
      potential_initial := h0
      potential_time_initial := h1
      tensor := completedBoundary ν ρ n.velocity n.pressure ψ
      tensor_eq := rfl
      admissible := hK
      stress_zero := fun t ht x => completedBoundary_stress_zero hn hψ hper hK ht x
      velocity_recovery := fun t ht => completedBoundary_velocity_recovery hn hψ hper ht
      pressure_recovery := completedBoundary_pressure_recovery hn hψ hper hK }⟩

end
end NSEGR.Assembly
