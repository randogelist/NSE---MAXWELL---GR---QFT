import GRAdapter.Germs

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace NSEGR
noncomputable section

/-- Equality of entire boundary tensor slices implies equality of the
reconstructed velocity on the same time germ. -/
theorem boundaryVelocity_congr_eventually {t0 : ℝ} (K L : BoundaryTensor)
    (h : K =ᶠ[𝓝 t0] L) :
    boundaryVelocity K =ᶠ[𝓝 t0] boundaryVelocity L := by
  filter_upwards [h] with t ht
  exact boundaryVelocity_congr_slice K L t ht

/-- The time derivatives in the pressure reconstruction are also local.
The full-slice hypothesis is not replaced by a pointwise-in-x neighborhood. -/
theorem boundaryPressure_congr_eventually {t0 : ℝ} (ρ : ℝ)
    (K L : BoundaryTensor) (h : K =ᶠ[𝓝 t0] L) :
    boundaryPressure ρ K =ᶠ[𝓝 t0] boundaryPressure ρ L := by
  filter_upwards [h.eventuallyEq_nhds] with t hlocal
  have hslice : K t = L t := hlocal.eq_of_nhds
  have hv := boundaryVelocity_congr_slice K L t hslice
  have hpotential : boundaryPotential K =ᶠ[𝓝 t] boundaryPotential L := by
    filter_upwards [hlocal] with s hs
    exact boundaryPotential_congr_slice K L s hs
  funext x
  have hx : (fun s : ℝ => boundaryPotential K s x) =ᶠ[𝓝 t]
      (fun s : ℝ => boundaryPotential L s x) := by
    filter_upwards [hpotential] with s hs
    exact congrFun hs x
  have hsecond :
      scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t x =
      scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential L)) t x := by
    exact hx.deriv.deriv_eq
  simp only [boundaryPressure, hslice, hv, hsecond]

theorem boundaryFields_sameFlow_of_eventually_eq {t0 : ℝ} (ρ : ℝ)
    (K L : BoundaryTensor) (h : K =ᶠ[𝓝 t0] L) :
    SameFlowAt t0 (boundaryVelocity K) (boundaryPressure ρ K)
      (boundaryVelocity L) (boundaryPressure ρ L) := by
  unfold SameFlowAt
  filter_upwards [boundaryVelocity_congr_eventually K L h,
    boundaryPressure_congr_eventually ρ K L h] with t hv hp
  refine ⟨hv, 0, ?_⟩
  intro x
  simpa only [add_zero] using congrFun hp x


theorem origin_pressure_gauge_analytic
    {t0 δ ε : ℝ} {u v : Velocity} {p q : Pressure}
    (hp : AnalyticPeriodicPair t0 δ u p)
    (hq : AnalyticPeriodicPair t0 ε v q) :
    AnalyticOnNhd ℝ (fun t : ℝ => p t (0 : Vec) - q t (0 : Vec))
      (timeInterval t0 δ ∩ timeInterval t0 ε) := by
  intro t ht
  have hap : AnalyticAt ℝ (fun z : ℝ × Vec => p z.1 z.2) (t, (0 : Vec)) :=
    hp.pressure_analytic (t, (0 : Vec)) ht.1
  have haq : AnalyticAt ℝ (fun z : ℝ × Vec => q z.1 z.2) (t, (0 : Vec)) :=
    hq.pressure_analytic (t, (0 : Vec)) ht.2
  simpa only [Pi.sub_def] using hap.curry_left.sub haq.curry_left

/-- On the actual analytic carriers, the timewise constant-pressure relation
is exactly an analytic time-gauge relation on a common neighborhood. -/
theorem sameFlowAt_iff_analytic_pressure_gauge
    {t0 δ ε : ℝ} {u v : Velocity} {p q : Pressure}
    (hp : AnalyticPeriodicPair t0 δ u p)
    (hq : AnalyticPeriodicPair t0 ε v q) :
    SameFlowAt t0 u p v q ↔
      ∃ a : ℝ → ℝ,
        AnalyticOnNhd ℝ a (timeInterval t0 δ ∩ timeInterval t0 ε) ∧
          ∀ᶠ t in 𝓝 t0, u t = v t ∧ ∀ x : Vec, p t x = q t x + a t := by
  constructor
  · intro h
    refine ⟨fun t => p t (0 : Vec) - q t (0 : Vec),
      origin_pressure_gauge_analytic hp hq, ?_⟩
    exact (sameFlowAt_iff_origin_gauge t0 u v p q).mp h
  · rintro ⟨a, ha, heq⟩
    unfold SameFlowAt
    filter_upwards [heq] with t ht
    exact ⟨ht.1, a t, ht.2⟩


/-- Spatial coordinates in the fixed bulk marking `(r,t,x1,x2,x3)`. -/
def bulkSpatialCoordinates (z : Bulk) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => z i.succ.succ)

theorem bulkPoint_coordinates (z : Bulk) :
    bulkPoint (z 0) (z 1) (bulkSpatialCoordinates z) = z := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · rfl

/-- The uniform full-spatial-slice germ induces the actual bulk germ at
every spatial point. No regularity of either metric is used. -/
theorem metric_eventuallyEq_of_fullSlices {r t : ℝ} {g h : Metric}
    (hslice : ∀ᶠ rt : ℝ × ℝ in 𝓝 (r, t), ∀ x : Vec,
      g (bulkPoint rt.1 rt.2 x) = h (bulkPoint rt.1 rt.2 x))
    (x : Vec) : g =ᶠ[𝓝 (bulkPoint r t x)] h := by
  have hcontinuous : Continuous (fun z : Bulk => (z 0, z 1)) := by
    fun_prop
  have hprojection : Tendsto (fun z : Bulk => (z 0, z 1))
      (𝓝 (bulkPoint r t x)) (𝓝 (r, t)) := by
    simpa only [bulkPoint_radial, bulkPoint_time] using
      hcontinuous.tendsto (bulkPoint r t x)
  filter_upwards [hprojection.eventually hslice] with z hz
  simpa only [bulkPoint_coordinates] using hz (bulkSpatialCoordinates z)

/-- Metric germs determine the actual normal first-jet tensor as a
uniform full-spatial-slice time germ. Locality of `fderiv` requires no
differentiability premise. -/
theorem sameMetricAt_boundaryK {t0 : ℝ} {g h : Metric}
    (hmetric : SameMetricAt t0 g h) :
    boundaryK g =ᶠ[𝓝 t0] boundaryK h := by
  have hslices : ∀ᶠ rt : ℝ × ℝ in 𝓝 ((0 : ℝ), t0),
      ∀ᶠ rs : ℝ × ℝ in 𝓝 rt, ∀ x : Vec,
        g (bulkPoint rs.1 rs.2 x) = h (bulkPoint rs.1 rs.2 x) :=
    hmetric.eventually_nhds
  have htime : Tendsto (fun t : ℝ => ((0 : ℝ), t))
      (𝓝 t0) (𝓝 ((0 : ℝ), t0)) :=
    (continuous_const.prodMk continuous_id).tendsto t0
  filter_upwards [htime.eventually hslices] with t ht
  funext x a b
  have hbulk := metric_eventuallyEq_of_fullSlices ht x
  have hcomponent :
      (fun z : Bulk => g z (boundaryIndex a) (boundaryIndex b))
        =ᶠ[𝓝 (bulkPoint 0 t x)]
      (fun z : Bulk => h z (boundaryIndex a) (boundaryIndex b)) := by
    filter_upwards [hbulk] with z hz
    exact congrArg (fun M : BulkMatrix => M (boundaryIndex a) (boundaryIndex b)) hz
  unfold boundaryK bulkPartial
  rw [hcomponent.fderiv_eq (𝕜 := ℝ)]

/-- Native descent of reconstructed fields to metric germs; this discharges
the former `reverse_respects` law without an additional analytic hypothesis. -/
theorem sameMetricAt_boundaryFields {t0 : ℝ} (ρ : ℝ) {g h : Metric}
    (hmetric : SameMetricAt t0 g h) :
    SameFlowAt t0 (boundaryVelocity (boundaryK g))
      (boundaryPressure ρ (boundaryK g))
      (boundaryVelocity (boundaryK h)) (boundaryPressure ρ (boundaryK h)) :=
  boundaryFields_sameFlow_of_eventually_eq ρ (boundaryK g) (boundaryK h)
    (sameMetricAt_boundaryK hmetric)


end
end NSEGR
