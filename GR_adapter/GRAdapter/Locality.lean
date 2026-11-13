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
  simpa only [Pi.sub_apply] using hap.curry_left.sub haq.curry_left

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


end
end NSEGR
