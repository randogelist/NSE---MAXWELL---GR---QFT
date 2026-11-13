import GRAssembly.NativeGluingTranslation
import GRAdapter.Contracts

/-! LI01 to one actual periodic scalar cylinder. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR.Assembly
noncomputable section

theorem scalarNormalGerm_of_hamiltonian_nativeGluing
    {ν ρ t0 : ℝ} {u : Velocity} {p ψ : Pressure} {x0 : Vec}
    (hρ : ρ ≠ 0)
    (ha : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t0, x0))
    (hi : ∀ᶠ x in 𝓝 x0, ψ t0 x = 0)
    (ht : ∀ᶠ x in 𝓝 x0, scalarLocalTimeDerivative ψ t0 x = 0)
    (hH : ∀ᶠ z in 𝓝 (t0, x0),
      boundaryHamiltonian (completedBoundary ν ρ u p ψ) z.1 z.2 = 0) :
    ScalarNormalGerm ν ρ u p t0 x0 ψ := by
  have hc : ContinuousAt
      (fun z : ℝ × Vec => ρ + scalarLaplacian (ψ z.1) z.2) (t0, x0) :=
    (analyticAt_const.add (analyticAt_scalarLaplacian_joint ha)).continuousAt
  have hne : ρ + scalarLaplacian (ψ t0) x0 ≠ 0 := by
    simpa only [scalarLaplacian_eq_zero_of_germ_zero hi, add_zero] using hρ
  refine ⟨ha, hi, ht, ?_⟩
  filter_upwards [hc.eventually_ne hne, hH] with z hz hHz
  exact (completedBoundary_hamiltonian_zero_iff_scalar_normal
    ν ρ u p ψ z.1 z.2 hz).mp hHz

structure ScalarGluingLaw (ν ρ t0 δ : ℝ) (u : Velocity) (p : Pressure)
    (f : ℝ × Vec → ℝ) (z : ℝ × Vec) : Prop where
  time_mem : z.1 ∈ timeInterval t0 δ
  analytic : AnalyticAt ℝ f z
  hamiltonian : boundaryHamiltonian
    (completedBoundary ν ρ u p (fun t x => f (t, x))) z.1 z.2 = 0
  initial : z.1 = t0 → f z = 0
  time_initial : z.1 = t0 → jointTime f z = 0

theorem ScalarGluingLaw.congr
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : ScalarGluingLaw ν ρ t0 δ u p f z) (he : f =ᶠ[𝓝 z] g) :
    ScalarGluingLaw ν ρ t0 δ u p g z := by
  refine ⟨hf.time_mem, hf.analytic.congr he, ?_, ?_, ?_⟩
  · rw [← boundaryHamiltonian_joint_congr he]
    exact hf.hamiltonian
  · intro ht
    rw [← he.self_of_nhds]
    exact hf.initial ht
  · intro ht
    rw [← jointTime_congr he]
    exact hf.time_initial ht

theorem ScalarGluingLaw.translate
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    (hpair : AnalyticPeriodicPair t0 δ u p)
    (f : ℝ × Vec → ℝ) (z : ℝ × Vec) (n : Frequency)
    (hf : ScalarGluingLaw ν ρ t0 δ u p f
      (z.1, z.2 - integerSpatialShift n)) :
    ScalarGluingLaw ν ρ t0 δ u p (spatialTranslate f n) z := by
  have hm : AnalyticAt ℝ
      (fun w : ℝ × Vec => (w.1, w.2 - integerSpatialShift n)) z :=
    analyticAt_fst.prod (analyticAt_snd.sub analyticAt_const)
  have ha : AnalyticAt ℝ (spatialTranslate f n) z :=
    hf.analytic.comp (f := fun w : ℝ × Vec => (w.1, w.2 - integerSpatialShift n))
      (x := z) hm
  refine ⟨hf.time_mem, ha, ?_, hf.initial, hf.time_initial⟩
  change boundaryHamiltonian (completedBoundary ν ρ u p
    (fun t x => f (t, x - integerSpatialShift n))) z.1 z.2 = 0
  unfold boundaryHamiltonian
  rw [completedBoundary_spatial_sub (ν := ν) (ρ := ρ)
    (ψ := fun t x => f (t, x))
    (hpair.periodic_velocity z.1 hf.time_mem) (hpair.periodic_pressure z.1 hf.time_mem) n z.2]
  exact hf.hamiltonian

theorem scalarGluingLaw_germ_of_normal
    {ν ρ t0 δ : ℝ} {u : Velocity} {p ψ : Pressure} {x0 : Vec}
    (hρ : ρ ≠ 0) (hδ : 0 < δ)
    (hψ : ScalarNormalGerm ν ρ u p t0 x0 ψ) :
    ∀ᶠ z in 𝓝 (t0, x0),
      ScalarGluingLaw ν ρ t0 δ u p (fun z => ψ z.1 z.2) z := by
  have htmem : ∀ᶠ t in 𝓝 t0, t ∈ timeInterval t0 δ := timeInterval_mem_nhds t0 δ hδ
  have htime := htmem.prod_inl_nhds x0
  have hini := hψ.initial.prod_inr_nhds t0
  have hti := hψ.time_initial.prod_inr_nhds t0
  filter_upwards [htime, hψ.analytic.eventually_analyticAt,
    hψ.hamiltonian hρ, hini, hti] with z hz ha hH hi ht
  refine ⟨hz, ha, hH, ?_, ?_⟩
  · intro he
    change ψ z.1 z.2 = 0
    rwa [he]
  · intro he
    change scalarLocalTimeDerivative ψ z.1 z.2 = 0
    rwa [he]

theorem scalarNormalGerm_of_gluingLaw
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure} {f : ℝ × Vec → ℝ} {x0 : Vec}
    (hρ : ρ ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (t0, x0), ScalarGluingLaw ν ρ t0 δ u p f z) :
    ScalarNormalGerm ν ρ u p t0 x0 (fun t x => f (t, x)) := by
  have hm : Tendsto (fun x : Vec => (t0, x)) (𝓝 x0) (𝓝 (t0, x0)) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto
  apply scalarNormalGerm_of_hamiltonian_nativeGluing hρ hf.self_of_nhds.analytic
  · filter_upwards [hm.eventually hf] with x hx
    exact hx.initial rfl
  · filter_upwards [hm.eventually hf] with x hx
    exact hx.time_initial rfl
  · exact hf.mono (fun _ hz => hz.hamiltonian)

/-- Concrete periodic scalar completion cylinder derived solely from LI01.
The radius may shrink, exactly as required by CompletedBoundary. -/
theorem scalar_periodic_cylinder_of_literatureCK
    (input : LiteratureAnalyticCKInput)
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    (hρ : ρ ≠ 0) (hpair : AnalyticPeriodicPair t0 δ u p) :
    ∃ (d : ℝ) (ψ : Pressure), 0 < d ∧ d ≤ δ ∧
      AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 d) ∧
      (∀ t ∈ timeInterval t0 d, SpatialPeriodic (ψ t)) ∧
      (∀ x, ψ t0 x = 0) ∧
      (∀ x, scalarLocalTimeDerivative ψ t0 x = 0) ∧
      (∀ t ∈ timeInterval t0 d, ∀ x,
        boundaryHamiltonian (completedBoundary ν ρ u p ψ) t x = 0) := by
  have hex (x : Vec) (_hx : x ∈ unitCube) :
      ∃ f : ℝ × Vec → ℝ,
        ∀ᶠ z in 𝓝 (t0, x), ScalarGluingLaw ν ρ t0 δ u p f z := by
    obtain ⟨ψ, hψ⟩ := scalarNormalGerm_exists input hρ hpair x
    exact ⟨(fun z => ψ z.1 z.2), scalarGluingLaw_germ_of_normal hρ hpair.radius_pos hψ⟩
  have hlocality (f g : ℝ × Vec → ℝ) (z : ℝ × Vec)
      (he : f =ᶠ[𝓝 z] g) :
      ScalarGluingLaw ν ρ t0 δ u p f z ↔ ScalarGluingLaw ν ρ t0 δ u p g z :=
    ⟨fun hf => hf.congr he, fun hg => hg.congr he.symm⟩
  have huniq (f g : ℝ × Vec → ℝ) (x : Vec)
      (hf : ∀ᶠ z in 𝓝 (t0, x), ScalarGluingLaw ν ρ t0 δ u p f z)
      (hg : ∀ᶠ z in 𝓝 (t0, x), ScalarGluingLaw ν ρ t0 δ u p g z) :
      f =ᶠ[𝓝 (t0, x)] g := by
    have ht : t0 ∈ timeInterval t0 δ := by
      constructor <;> linarith [hpair.radius_pos]
    exact scalar_normalized_germ_unique input hρ
      (hpair.velocity_analytic (t0, x) ht) (hpair.pressure_analytic (t0, x) ht)
      (scalarNormalGerm_of_gluingLaw hρ hf) (scalarNormalGerm_of_gluingLaw hρ hg)
  obtain ⟨W, hW, htW, f, hperiodic, hlaw⟩ :=
    periodic_law_of_unique_local_germs (ScalarGluingLaw ν ρ t0 δ u p)
      hex hlocality (ScalarGluingLaw.translate hpair) huniq (0 : ℝ)
  obtain ⟨d, hd, hdδ, hsub⟩ := positive_timeInterval_subset hpair.radius_pos (hW.mem_nhds htW)
  refine ⟨d, (fun t x => f (t, x)), hd, hdδ, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hlaw z.1 (hsub hz) z.2).analytic
  · intro t ht
    exact hperiodic t (hsub ht)
  · intro x
    exact (hlaw t0 htW x).initial rfl
  · intro x
    exact (hlaw t0 htW x).time_initial rfl
  · intro t ht x
    exact (hlaw t (hsub ht) x).hamiltonian

theorem scalarLaplacian_spatial_sub (f : ScalarField) (c : Vec) (x : Vec) :
    scalarLaplacian (fun y => f (y - c)) x = scalarLaplacian f (x - c) := by
  exact congrArg (fun T : Tensor4 => T 0 0)
    (scalarCompletionUpper_spatial_sub (fun _ => f) c 0 x)

theorem scalarLaplacian_periodic_nativeGluing {f : ScalarField} (hf : SpatialPeriodic f) :
    SpatialPeriodic (scalarLaplacian f) := by
  have hs (n : Frequency) (x : Vec) :
      scalarLaplacian f (x - integerSpatialShift n) = scalarLaplacian f x := by
    rw [← scalarLaplacian_spatial_sub f (integerSpatialShift n) x]
    have he : (fun y => f (y - integerSpatialShift n)) = f :=
      funext (spatialPeriodic_sub_integer hf n)
    rw [he]
  intro x i
  have he := hs (Pi.single i (1 : ℤ)) (x + unitVector i)
  simpa only [integerSpatialShift_single, add_sub_cancel_right] using he.symm

/-- The complete scalar normal-form cylinder, including a uniform quantitative
noncharacteristic bound and the actual second-order equation. -/
theorem scalar_periodic_normal_cylinder_of_literatureCK
    (input : LiteratureAnalyticCKInput)
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    (hρ : ρ ≠ 0) (hpair : AnalyticPeriodicPair t0 δ u p) :
    ∃ (d : ℝ) (ψ : Pressure), 0 < d ∧ d ≤ δ ∧
      AnalyticOnNhd ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (spacetimeSlab t0 d) ∧
      (∀ t ∈ timeInterval t0 d, SpatialPeriodic (ψ t)) ∧
      (∀ x, ψ t0 x = 0) ∧
      (∀ x, scalarLocalTimeDerivative ψ t0 x = 0) ∧
      (∀ t ∈ timeInterval t0 d, ∀ x,
        |ρ| / 2 < |ρ + scalarLaplacian (ψ t) x|) ∧
      (∀ t ∈ timeInterval t0 d, ∀ x,
        scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x =
          scalarJetRHS ρ (fun i => u t x i) (nseSpatialSource3 ν u p t x)
            (scalarHessian (ψ t) x)
            (fun i => gradient (scalarLocalTimeDerivative ψ t) x i)) ∧
      (∀ t ∈ timeInterval t0 d, ∀ x,
        boundaryHamiltonian (completedBoundary ν ρ u p ψ) t x = 0) := by
  obtain ⟨d0, ψ, hd0, hd0δ, ha, hper, hi, hti, hH⟩ :=
    scalar_periodic_cylinder_of_literatureCK (ν := ν) input hρ hpair
  have hnorm : 0 < |ρ| / 2 := half_pos (abs_pos.mpr hρ)
  have hlocal (x : Vec) (_hx : x ∈ unitCube) :
      ∀ᶠ z : ℝ × Vec in 𝓝 (t0, x),
        |scalarLaplacian (ψ z.1) z.2| < |ρ| / 2 := by
    have ht0 : t0 ∈ timeInterval t0 d0 := by constructor <;> linarith
    have hc := (analyticAt_scalarLaplacian_joint (ha (t0, x) ht0)).continuousAt.abs
    apply hc.eventually (p := fun y : ℝ => y < |ρ| / 2)
    apply gt_mem_nhds
    rw [scalarLaplacian_eq_zero_of_germ_zero (Eventually.of_forall hi), abs_zero]
    exact hnorm
  have hbound : ∀ᶠ t in 𝓝 t0, ∀ x ∈ unitCube,
      |scalarLaplacian (ψ t) x| < |ρ| / 2 :=
    isCompact_unitCube.eventually_forall_of_forall_eventually hlocal
  obtain ⟨d, hd, hdd0, hsub⟩ := positive_timeInterval_subset hd0
    (hbound.and (timeInterval_mem_nhds t0 d0 hd0))
  have hfull (t : ℝ) (ht : t ∈ timeInterval t0 d) (x : Vec) :
      |scalarLaplacian (ψ t) x| < |ρ| / 2 := by
    have hh := hsub ht
    rw [spatialPeriodic_eq_cellRepresentative (scalarLaplacian_periodic_nativeGluing (hper t hh.2)) x]
    exact hh.1 _ (spatialCellRepresentative_mem_unitCube x)
  have hnonchar (t : ℝ) (ht : t ∈ timeInterval t0 d) (x : Vec) :
      |ρ| / 2 < |ρ + scalarLaplacian (ψ t) x| := by
    have hb := hfull t ht x
    have hab := abs_add_le (ρ + scalarLaplacian (ψ t) x) (-scalarLaplacian (ψ t) x)
    simp only [add_neg_cancel_right, abs_neg] at hab
    linarith
  refine ⟨d, ψ, hd, hdd0.trans hd0δ, ?_, ?_, hi, hti, hnonchar, ?_, ?_⟩
  · intro z hz
    exact ha z (hsub hz).2
  · intro t ht
    exact hper t (hsub ht).2
  · intro t ht x
    have hn : ρ + scalarLaplacian (ψ t) x ≠ 0 :=
      abs_pos.mp (hnorm.trans (hnonchar t ht x))
    exact (completedBoundary_hamiltonian_zero_iff_scalar_normal ν ρ u p ψ t x hn).mp
      (hH t (hsub ht).2 x)
  · intro t ht x
    exact hH t (hsub ht).2 x

end
end NSEGR.Assembly
