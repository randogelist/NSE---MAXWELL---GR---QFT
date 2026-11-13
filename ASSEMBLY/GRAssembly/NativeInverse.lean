import GRAssembly.ScalarJet
import GRAssembly.PressureGauge
import GRAdapter.GaussianUniqueness
import NSEGRReverse

/-!
Actual normalized scalar uniqueness, pressure-gauge descent and arbitrary-choice
inverse laws. Every occurrence of a completion is the original native record;
no image-defined target or compatible-choice premise is introduced.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2000000

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Assembly
noncomputable section

/-- Hamiltonian and zero Cauchy data recover the literal scalar CK equation. -/
theorem scalarNormalGerm_of_hamiltonian
    {ν ρ t0 : ℝ} {u : Velocity} {p ψ : Pressure} {x0 : Vec}
    (hρ : ρ ≠ 0)
    (ha : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t0, x0))
    (hi : ∀ᶠ x in 𝓝 x0, ψ t0 x = 0)
    (hti : ∀ᶠ x in 𝓝 x0, scalarLocalTimeDerivative ψ t0 x = 0)
    (hH : ∀ᶠ z in 𝓝 (t0, x0),
      boundaryHamiltonian (completedBoundary ν ρ u p ψ) z.1 z.2 = 0) :
    ScalarNormalGerm ν ρ u p t0 x0 ψ := by
  have hdenA : AnalyticAt ℝ
      (fun z : ℝ × Vec => ρ + scalarLaplacian (ψ z.1) z.2) (t0, x0) :=
    analyticAt_const.add (analyticAt_scalarLaplacian_joint ha)
  have hden : ∀ᶠ z in 𝓝 (t0, x0),
      ρ + scalarLaplacian (ψ z.1) z.2 ≠ 0 := by
    apply hdenA.continuousAt.eventually_ne
    simpa only [scalarLaplacian_eq_zero_of_germ_zero hi, add_zero] using hρ
  refine ⟨ha, hi, hti, ?_⟩
  filter_upwards [hH, hden] with z hz hd
  exact (completedBoundary_hamiltonian_zero_iff_scalar_normal
    ν ρ u p ψ z.1 z.2 hd).1 hz

/-- This applies to every original completion witness, regardless of its choice. -/
theorem completedBoundary_scalarNormalGerm
    {ν ρ t0 : ℝ} {n : NSERepresentative ν t0}
    (c : CompletedBoundary ν ρ t0 n) (hρ : ρ ≠ 0) (x0 : Vec) :
    ScalarNormalGerm ν ρ n.velocity n.pressure t0 x0 c.potential := by
  have ht : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 c.timeRadius :=
    timeInterval_mem_nhds t0 c.timeRadius c.admissible.radius_pos
  apply scalarNormalGerm_of_hamiltonian hρ
    (c.potential_analytic (t0, x0) ht.self_of_nhds)
    (Eventually.of_forall c.potential_initial)
    (Eventually.of_forall c.potential_time_initial)
  filter_upwards [ht.prod_inl_nhds x0] with z hz
  rw [← c.tensor_eq]
  exact c.admissible.hamiltonian z.1 hz z.2

/-- Full-slice equality retains its uniform neighborhood after ordinary time differentiation. -/
theorem scalarLocalTimeDerivative_congr_eventually
    {t0 : ℝ} {ψ φ : Pressure} (h : ψ =ᶠ[𝓝 t0] φ) :
    scalarLocalTimeDerivative ψ =ᶠ[𝓝 t0] scalarLocalTimeDerivative φ := by
  filter_upwards [h.eventuallyEq_nhds] with t ht
  funext x
  have hx : (fun s : ℝ => ψ s x) =ᶠ[𝓝 t] (fun s : ℝ => φ s x) := by
    filter_upwards [ht] with s hs
    exact congrFun hs x
  exact hx.deriv_eq

/-- The actual completed tensor is local in all full spatial input slices. -/
theorem completedBoundary_congr_eventually
    {ν ρ t0 : ℝ} {u v : Velocity} {p q ψ φ : Pressure}
    (hu : u =ᶠ[𝓝 t0] v) (hp : p =ᶠ[𝓝 t0] q)
    (hψ : ψ =ᶠ[𝓝 t0] φ) :
    completedBoundary ν ρ u p ψ =ᶠ[𝓝 t0] completedBoundary ν ρ v q φ := by
  have ht := scalarLocalTimeDerivative_congr_eventually hψ
  have htt := scalarLocalTimeDerivative_congr_eventually ht
  filter_upwards [hu, hp, hψ, ht, htt] with t hut hpt hψt hdt hddt
  funext x
  simp only [completedBoundary, conservedSourceUpper, scalarCompletionUpper,
    hut, hpt, hψt, hdt, hddt]

/-- Velocity and pressure enter the source through the current full spatial slice. -/
theorem completedBoundary_input_congr_slice
    {ν ρ t : ℝ} {u v : Velocity} {p q ψ : Pressure}
    (hu : u t = v t) (hp : p t = q t) :
    completedBoundary ν ρ u p ψ t = completedBoundary ν ρ v q ψ t := by
  funext x
  simp only [completedBoundary, conservedSourceUpper, hu, hp]

/-- LI01 and LI02 give forward descent for arbitrary supplied completion laws. -/
theorem forward_respects_of_literature
    (ck : LiteratureAnalyticCKInput) (gj : LiteratureGaussianJetInput)
    {ν ρ t0 : ℝ} (hρ : ρ ≠ 0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0)
    (a b : NSERepresentative ν t0)
    (hab : SameFlowAt t0 a.velocity a.pressure b.velocity b.pressure) :
    SameMetricAt t0 (forwardRepresentative c r a).metric
      (forwardRepresentative c r b).metric := by
  let ca := chosenBoundary c a
  let cb := chosenBoundary c b
  have hta : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 a.radius :=
    timeInterval_mem_nhds t0 a.radius a.solution.radius_pos
  have htb : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 b.radius :=
    timeInterval_mem_nhds t0 b.radius b.solution.radius_pos
  have htca : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 ca.timeRadius :=
    timeInterval_mem_nhds t0 ca.timeRadius ca.admissible.radius_pos
  have htcb : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 cb.timeRadius :=
    timeInterval_mem_nhds t0 cb.timeRadius cb.admissible.radius_pos
  obtain ⟨γ, hγ, hflow⟩ := (sameFlowAt_iff_analytic_pressure_gauge
    a.solution.toAnalyticPeriodicPair b.solution.toAnalyticPeriodicPair).1 hab
  have hγ0 : AnalyticAt ℝ γ t0 := hγ t0 ⟨hta.self_of_nhds, htb.self_of_nhds⟩
  obtain ⟨A, hA, hA0, hA1, hA2⟩ := analytic_double_primitive_of_literatureCK ck hγ0
  let φ : Pressure := fun t x => cb.potential t x - A t
  have hKgauge : completedBoundary ν ρ a.velocity a.pressure φ =ᶠ[𝓝 t0] cb.tensor := by
    filter_upwards [htcb, hflow, hA.eventually_analyticAt, hA2] with t ht hf ha ha2
    have hp : a.pressure t = (fun s x => b.pressure s x + γ s) t := funext hf.2
    rw [completedBoundary_input_congr_slice (ν := ν) (ρ := ρ) (ψ := φ)
      (q := fun s x => b.pressure s x + γ s) hf.1 hp]
    funext x
    calc
      completedBoundary ν ρ b.velocity (fun s x => b.pressure s x + γ s) φ t x =
          completedBoundary ν ρ b.velocity b.pressure cb.potential t x :=
        completedBoundary_pressure_gauge (cb.potential_analytic (t, x) ht) ha ha2
      _ = cb.tensor t x := by rw [cb.tensor_eq]
  have hφnormal (x0 : Vec) :
      ScalarNormalGerm ν ρ a.velocity a.pressure t0 x0 φ := by
    have hcbA := cb.potential_analytic (t0, x0) htcb.self_of_nhds
    have hφA : AnalyticAt ℝ (fun z : ℝ × Vec => φ z.1 z.2) (t0, x0) :=
      hcbA.sub (hA.comp analyticAt_fst)
    apply scalarNormalGerm_of_hamiltonian hρ hφA
    · apply Eventually.of_forall
      intro x
      simp only [φ, cb.potential_initial, hA0, sub_self]
    · apply Eventually.of_forall
      intro x
      have hx := cb.potential_analytic (t0, x) htcb.self_of_nhds
      change deriv (fun t => cb.potential t x - A t) t0 = 0
      rw [deriv_fun_sub hx.curry_left.differentiableAt hA.differentiableAt]
      change scalarLocalTimeDerivative cb.potential t0 x - deriv A t0 = 0
      rw [cb.potential_time_initial, hA1, sub_self]
    · filter_upwards [(hKgauge.and htcb).prod_inl_nhds x0] with z hz
      change lorentzSquare4 (completedBoundary ν ρ a.velocity a.pressure φ z.1 z.2) -
        (lorentzTrace4 (completedBoundary ν ρ a.velocity a.pressure φ z.1 z.2)) ^ 2 = 0
      rw [hz.1]
      exact cb.admissible.hamiltonian z.1 hz.2 z.2
  have hpot : ca.potential =ᶠ[𝓝 t0] φ := by
    have hp : ∀ᶠ t in 𝓝 t0,
        SpatialPeriodic (ca.potential t) ∧ SpatialPeriodic (φ t) := by
      filter_upwards [htca, htcb] with t hat hbt
      refine ⟨ca.potential_periodic t hat, ?_⟩
      intro x i
      change cb.potential t (x + unitVector i) - A t = cb.potential t x - A t
      rw [cb.potential_periodic t hbt x i]
    have heq := periodic_slice_germs_uniform hp (fun x _ =>
      scalar_normalized_germ_unique ck hρ
        (a.solution.velocity_analytic (t0, x) hta.self_of_nhds)
        (a.solution.pressure_analytic (t0, x) hta.self_of_nhds)
        (completedBoundary_scalarNormalGerm ca hρ x) (hφnormal x))
    exact heq.mono (fun _ ht => funext ht)
  have hK : ca.tensor =ᶠ[𝓝 t0] cb.tensor := by
    rw [ca.tensor_eq]
    exact (completedBoundary_congr_eventually
      (EventuallyEq.rfl : a.velocity =ᶠ[𝓝 t0] a.velocity)
      (EventuallyEq.rfl : a.pressure =ᶠ[𝓝 t0] a.pressure) hpot).trans hKgauge
  exact gaussianVacuum_sameMetricAt_of_literatureJet gj ca.admissible
    (forwardRepresentative c r a).geometry (forwardRepresentative c r b).geometry
    (forward_boundary_match_eventually c r a)
    ((forward_boundary_match_eventually c r b).trans hK.symm)

end
end NSEGR.Assembly
