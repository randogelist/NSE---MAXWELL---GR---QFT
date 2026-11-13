import GRAdapter.ScalarCompatibility
import GRAdapter.ScalarNormalForm
import ML012.Endpoint
import ML050.Endpoint

/-!
GC06: actual scalar second-order equation and normalized scalar uniqueness.
The only existence/uniqueness input is the literal LI01 signature. All
derivatives below are the native ordinary-time and spatial derivatives.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.Assembly
noncomputable section

def jointTime (f : ℝ × Vec → ℝ) (z : ℝ × Vec) : ℝ :=
  deriv (fun t : ℝ => f (t, z.2)) z.1

def jointSpace (f : ℝ × Vec → ℝ) (i : Fin 3) (z : ℝ × Vec) : ℝ :=
  fderiv ℝ (fun x : Vec => f (z.1, x)) z.2 (unitVector i)

theorem jointTime_congr {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (h : f =ᶠ[𝓝 z] g) : jointTime f z = jointTime g z := by
  have hm : Tendsto (fun t : ℝ => (t, z.2)) (𝓝 z.1) (𝓝 z) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  exact (h.comp_tendsto hm).deriv_eq

theorem jointSpace_congr {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (h : f =ᶠ[𝓝 z] g) (i : Fin 3) : jointSpace f i z = jointSpace g i z := by
  have hm : Tendsto (fun x : Vec => (z.1, x)) (𝓝 z.2) (𝓝 z) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i))
    (h.comp_tendsto hm).fderiv_eq

theorem jointTime_congr_germ {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (h : f =ᶠ[𝓝 z] g) : jointTime f =ᶠ[𝓝 z] jointTime g :=
  h.eventuallyEq_nhds.mono (fun _ hy => jointTime_congr hy)

theorem jointSpace_congr_germ {f g : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (h : f =ᶠ[𝓝 z] g) (i : Fin 3) : jointSpace f i =ᶠ[𝓝 z] jointSpace g i :=
  h.eventuallyEq_nhds.mono (fun _ hy => jointSpace_congr hy i)

theorem analyticAt_jointTime {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) : AnalyticAt ℝ (jointTime f) z := by
  apply (analyticAt_scalarJointPartial hf (1, 0)).congr
  filter_upwards [hf.eventually_analyticAt] with y hy
  exact (scalar_timeDerivative_eq_joint hy).symm

theorem analyticAt_jointSpace {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (i : Fin 3) : AnalyticAt ℝ (jointSpace f i) z := by
  apply (analyticAt_scalarJointPartial hf (0, unitVector i)).congr
  filter_upwards [hf.eventually_analyticAt] with y hy
  exact (scalar_spatialDerivative_eq_joint hy i).symm

theorem jointTime_jointSpace {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (i : Fin 3) :
    jointTime (jointSpace f i) z = jointSpace (jointTime f) i z := by
  have hs : jointSpace f i =ᶠ[𝓝 z] scalarJointPartial f (0, unitVector i) := by
    filter_upwards [hf.eventually_analyticAt] with y hy
    exact scalar_spatialDerivative_eq_joint hy i
  have ht : jointTime f =ᶠ[𝓝 z] scalarJointPartial f (1, 0) := by
    filter_upwards [hf.eventually_analyticAt] with y hy
    exact scalar_timeDerivative_eq_joint hy
  calc
    jointTime (jointSpace f i) z =
        jointTime (scalarJointPartial f (0, unitVector i)) z := jointTime_congr hs
    _ = scalarJointPartial (scalarJointPartial f (0, unitVector i)) (1, 0) z :=
      scalar_timeDerivative_eq_joint (analyticAt_scalarJointPartial hf _)
    _ = scalarJointPartial (scalarJointPartial f (1, 0)) (0, unitVector i) z :=
      scalarJointPartial_commute hf _ _
    _ = jointSpace (scalarJointPartial f (1, 0)) i z :=
      (scalar_spatialDerivative_eq_joint (analyticAt_scalarJointPartial hf _) i).symm
    _ = jointSpace (jointTime f) i z := jointSpace_congr ht.symm i

def scalarCKPotential (W : ℝ × Vec → ScalarCKState) : Pressure :=
  fun t x => W (t, x) 0

theorem scalarCK_coordinate_timeDerivative {W : ℝ × Vec → ScalarCKState}
    {z : ℝ × Vec} (hW : AnalyticAt ℝ W z) (k : Fin 5) :
    jointTime (fun y => W y k) z = deriv (fun t : ℝ => W (t, z.2)) z.1 k := by
  let ev : ScalarCKState →L[ℝ] ℝ := EuclideanSpace.proj k
  have hc : AnalyticAt ℝ (fun y => W y k) z := (ev.analyticAt _).comp hW
  have hm : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Vec)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have ht := hW.differentiableAt.hasFDerivAt.comp z.1 hm
  have ht' : deriv (fun t : ℝ => W (t, z.2)) z.1 = fderiv ℝ W z (1, 0) := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply] using ht.hasDerivAt.deriv
  rw [show jointTime (fun y => W y k) z =
    scalarJointPartial (fun y => W y k) (1, 0) z from scalar_timeDerivative_eq_joint hc]
  rw [scalarCK_coordinate_jointDerivative hW, ht']

theorem scalarCK_coordinate_spaceDerivative {W : ℝ × Vec → ScalarCKState}
    {z : ℝ × Vec} (hW : AnalyticAt ℝ W z) (k : Fin 5) (i : Fin 3) :
    fderiv ℝ (fun x => W (z.1, x)) z.2 (unitVector i) k =
      jointSpace (fun y => W y k) i z := by
  let ev : ScalarCKState →L[ℝ] ℝ := EuclideanSpace.proj k
  have hc : AnalyticAt ℝ (fun y => W y k) z := (ev.analyticAt _).comp hW
  rw [scalarCK_spatial_coordinate_derivative hW]
  exact (scalar_spatialDerivative_eq_joint hc i).symm

theorem scalarCK_potential_time_germ
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) :
    jointTime (fun z => W z 0) =ᶠ[𝓝 (t0, x0)] (fun z => W z 1) := by
  filter_upwards [hW.analytic.eventually_analyticAt, hW.equation] with z ha he
  rw [scalarCK_coordinate_timeDerivative ha, he, scalarCKRHS_potential]

theorem scalarCK_potential_initial
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) :
    ∀ᶠ x in 𝓝 x0, scalarCKPotential W t0 x = 0 := by
  filter_upwards [hW.initial] with x hx
  exact congrArg (fun a : ScalarCKState => a 0) hx

theorem scalarCK_potential_time_initial
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) :
    ∀ᶠ x in 𝓝 x0, scalarLocalTimeDerivative (scalarCKPotential W) t0 x = 0 := by
  have hm : Tendsto (fun x : Vec => (t0, x)) (𝓝 x0) (𝓝 (t0, x0)) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto
  filter_upwards [(scalarCK_potential_time_germ hW).comp_tendsto hm, hW.initial] with x ht hx
  exact ht.trans (congrArg (fun a : ScalarCKState => a 1) hx)

theorem scalarCK_secondOrder_equation
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) :
    ∀ᶠ z in 𝓝 (t0, x0),
      scalarLocalTimeDerivative (scalarLocalTimeDerivative (scalarCKPotential W)) z.1 z.2 =
        scalarJetRHS ρ (fun i => u z.1 z.2 i) (nseSpatialSource3 ν u p z.1 z.2)
          (scalarHessian (scalarCKPotential W z.1) z.2)
          (fun i => gradient (scalarLocalTimeDerivative (scalarCKPotential W) z.1) z.2 i) := by
  have ht := scalarCK_potential_time_germ hW
  have htt := jointTime_congr_germ ht
  have hb : ∀ i : Fin 3, ∀ᶠ z in 𝓝 (t0, x0),
      jointSpace (fun y => W y 1) i z = jointSpace (jointTime (fun y => W y 0)) i z :=
    fun i => jointSpace_congr_germ ht.symm i
  have hQ : ∀ i j : Fin 3, ∀ᶠ z in 𝓝 (t0, x0),
      jointSpace (fun y => W y (scalarCKGradientIndex j)) i z =
        jointSpace (jointSpace (fun y => W y 0) j) i z := by
    intro i j
    exact jointSpace_congr_germ (scalarCK_gradient_compatibility hW j) i
  have hb' := Filter.eventually_all.mpr hb
  have hQ' := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hQ i))
  filter_upwards [hW.analytic.eventually_analyticAt, hW.equation, htt, hb', hQ']
    with z ha he httz hbz hQz
  have hsp : scalarCKSpatialJet
      (z, (W z, fderiv ℝ (fun x => W (z.1, x)) z.2)) =
      scalarHessian (scalarCKPotential W z.1) z.2 := by
    ext i j
    change fderiv ℝ (fun x => W (z.1, x)) z.2 (unitVector i)
      (scalarCKGradientIndex j) = _
    rw [scalarCK_coordinate_spaceDerivative ha]
    exact hQz i j
  have hmi : scalarCKMixedJet
      (z, (W z, fderiv ℝ (fun x => W (z.1, x)) z.2)) =
      (fun i => gradient (scalarLocalTimeDerivative (scalarCKPotential W) z.1) z.2 i) := by
    funext i
    change fderiv ℝ (fun x => W (z.1, x)) z.2 (unitVector i) 1 = _
    rw [scalarCK_coordinate_spaceDerivative ha]
    exact hbz i
  change jointTime (jointTime (fun y => W y 0)) z = _
  rw [httz, scalarCK_coordinate_timeDerivative ha, he, scalarCKRHS_time, hsp, hmi]

/-- Actual normalized scalar solution germ, not a project completion law. -/
structure ScalarNormalGerm (ν ρ : ℝ) (u : Velocity) (p : Pressure)
    (t0 : ℝ) (x0 : Vec) (ψ : Pressure) : Prop where
  analytic : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t0, x0)
  initial : ∀ᶠ x in 𝓝 x0, ψ t0 x = 0
  time_initial : ∀ᶠ x in 𝓝 x0, scalarLocalTimeDerivative ψ t0 x = 0
  equation : ∀ᶠ z in 𝓝 (t0, x0),
    scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) z.1 z.2 =
      scalarJetRHS ρ (fun i => u z.1 z.2 i) (nseSpatialSource3 ν u p z.1 z.2)
        (scalarHessian (ψ z.1) z.2)
        (fun i => gradient (scalarLocalTimeDerivative ψ z.1) z.2 i)

theorem scalarCK_scalarNormalGerm
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) :
    ScalarNormalGerm ν ρ u p t0 x0 (scalarCKPotential W) where
  analytic := ((EuclideanSpace.proj (0 : Fin 5)).analyticAt _).comp hW.analytic
  initial := scalarCK_potential_initial hW
  time_initial := scalarCK_potential_time_initial hW
  equation := scalarCK_secondOrder_equation hW

def scalarStateOfPotential (ψ : Pressure) (z : ℝ × Vec) : ScalarCKState :=
  WithLp.toLp 2 (Fin.cases (ψ z.1 z.2)
    (Fin.cases (scalarLocalTimeDerivative ψ z.1 z.2)
      (fun i => gradient (ψ z.1) z.2 i)))

theorem analyticAt_scalarStateOfPotential {ψ : Pressure} {z : ℝ × Vec}
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) z) :
    AnalyticAt ℝ (scalarStateOfPotential ψ) z := by
  have hall : AnalyticAt ℝ
      (fun y : ℝ × Vec => (Fin.cases (ψ y.1 y.2)
        (Fin.cases (scalarLocalTimeDerivative ψ y.1 y.2)
          (fun i => gradient (ψ y.1) y.2 i)) : Fin 5 → ℝ)) z := by
    apply AnalyticAt.pi
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact hψ
    · refine Fin.cases ?_ (fun i => ?_) j
      · exact analyticAt_jointTime hψ
      · exact analyticAt_jointSpace hψ i
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).symm.analyticAt _).comp hall

theorem scalarStateOfPotential_solution
    {ν ρ t0 : ℝ} {u : Velocity} {p ψ : Pressure} {x0 : Vec}
    (hψ : ScalarNormalGerm ν ρ u p t0 x0 ψ) :
    LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 (scalarStateOfPotential ψ) := by
  refine ⟨analyticAt_scalarStateOfPotential hψ.analytic, ?_, ?_⟩
  · have hd := hψ.initial.fderiv (𝕜 := ℝ)
    filter_upwards [hψ.initial, hψ.time_initial, hd] with x h0 h1 hdx
    ext k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact h0
    · refine Fin.cases ?_ (fun i => ?_) j
      · exact h1
      · change fderiv ℝ (ψ t0) x (unitVector i) = 0
        rw [hdx]
        simp
  · filter_upwards [hψ.analytic.eventually_analyticAt, hψ.equation] with z ha he
    have hstate := analyticAt_scalarStateOfPotential ha
    have hsp : scalarCKSpatialJet
        (z, (scalarStateOfPotential ψ z,
          fderiv ℝ (fun x => scalarStateOfPotential ψ (z.1, x)) z.2)) =
        scalarHessian (ψ z.1) z.2 := by
      ext i j
      change fderiv ℝ (fun x => scalarStateOfPotential ψ (z.1, x)) z.2
        (unitVector i) (scalarCKGradientIndex j) = _
      rw [scalarCK_coordinate_spaceDerivative hstate]
      rfl
    have hmi : scalarCKMixedJet
        (z, (scalarStateOfPotential ψ z,
          fderiv ℝ (fun x => scalarStateOfPotential ψ (z.1, x)) z.2)) =
        (fun i => gradient (scalarLocalTimeDerivative ψ z.1) z.2 i) := by
      funext i
      change fderiv ℝ (fun x => scalarStateOfPotential ψ (z.1, x)) z.2 (unitVector i) 1 = _
      rw [scalarCK_coordinate_spaceDerivative hstate]
      rfl
    ext k
    rw [← scalarCK_coordinate_timeDerivative hstate]
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) j
      · rw [scalarCKRHS_time, hsp, hmi]
        exact he
      · rw [scalarCKRHS_gradient, scalarCK_coordinate_spaceDerivative hstate]
        exact jointTime_jointSpace ha i

theorem scalar_normalized_germ_unique
    (input : LiteratureAnalyticCKInput)
    {ν ρ t0 : ℝ} {u : Velocity} {p ψ φ : Pressure} {x0 : Vec}
    (hρ : ρ ≠ 0)
    (hu : AnalyticAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t0, x0))
    (hp : AnalyticAt ℝ (fun z : ℝ × Vec => p z.1 z.2) (t0, x0))
    (hψ : ScalarNormalGerm ν ρ u p t0 x0 ψ)
    (hφ : ScalarNormalGerm ν ρ u p t0 x0 φ) :
    (fun z : ℝ × Vec => ψ z.1 z.2) =ᶠ[𝓝 (t0, x0)]
      (fun z : ℝ × Vec => φ z.1 z.2) := by
  obtain ⟨W, _, huniq⟩ := input.exists_unique 3 5 (by norm_num) (by norm_num)
    (scalarCKRHS ν ρ u p) (fun _ : Vec => (0 : ScalarCKState)) t0 x0
    analyticAt_const (analyticAt_scalarCKRHS hu hp
      (scalarCK_zero_initial_noncharacteristic hρ x0))
  have hstates := (huniq _ (scalarStateOfPotential_solution hψ)).symm.trans
    (huniq _ (scalarStateOfPotential_solution hφ))
  filter_upwards [hstates] with z hz
  exact congrArg (fun a : ScalarCKState => a 0) hz

theorem scalarNormalGerm_exists
    (input : LiteratureAnalyticCKInput)
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    (hρ : ρ ≠ 0) (hpair : AnalyticPeriodicPair t0 δ u p) (x0 : Vec) :
    ∃ ψ : Pressure, ScalarNormalGerm ν ρ u p t0 x0 ψ := by
  obtain ⟨W, hW, _⟩ := scalarCK_exists_unique_firstOrder input hρ hpair x0
  exact ⟨scalarCKPotential W, scalarCK_scalarNormalGerm hW⟩

theorem scalarHessian_eq_zero_of_germ_zero {f : ScalarField} {x : Vec}
    (h : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ))) : scalarHessian f x = 0 := by
  ext i j
  have hd : (fun y : Vec => fderiv ℝ f y (unitVector j)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
    simp
  have hdd := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) hd.fderiv_eq
  simpa only [scalarHessian, fderiv_const, ContinuousLinearMap.zero_apply,
    Matrix.zero_apply] using hdd

theorem scalarLaplacian_eq_zero_of_germ_zero {f : ScalarField} {x : Vec}
    (h : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ))) : scalarLaplacian f x = 0 := by
  rw [← trace3_scalarHessian, scalarHessian_eq_zero_of_germ_zero h, trace3_zero]

theorem analyticAt_scalarLaplacian_joint {ψ : Pressure} {z : ℝ × Vec}
    (hψ : AnalyticAt ℝ (fun y : ℝ × Vec => ψ y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => scalarLaplacian (ψ y.1) y.2) z := by
  exact analyticAt_fin3_sum (fun i =>
    analyticAt_jointSpace (analyticAt_jointSpace hψ i) i)

theorem ScalarNormalGerm.noncharacteristic
    {ν ρ t0 : ℝ} {u : Velocity} {p ψ : Pressure} {x0 : Vec}
    (hψ : ScalarNormalGerm ν ρ u p t0 x0 ψ) (hρ : ρ ≠ 0) :
    ∀ᶠ z in 𝓝 (t0, x0), ρ + scalarLaplacian (ψ z.1) z.2 ≠ 0 := by
  have ha : AnalyticAt ℝ
      (fun z : ℝ × Vec => ρ + scalarLaplacian (ψ z.1) z.2) (t0, x0) :=
    analyticAt_const.add (analyticAt_scalarLaplacian_joint hψ.analytic)
  apply ha.continuousAt.eventually_ne
  simpa only [scalarLaplacian_eq_zero_of_germ_zero hψ.initial, add_zero] using hρ

theorem ScalarNormalGerm.hamiltonian
    {ν ρ t0 : ℝ} {u : Velocity} {p ψ : Pressure} {x0 : Vec}
    (hψ : ScalarNormalGerm ν ρ u p t0 x0 ψ) (hρ : ρ ≠ 0) :
    ∀ᶠ z in 𝓝 (t0, x0),
      boundaryHamiltonian (completedBoundary ν ρ u p ψ) z.1 z.2 = 0 := by
  filter_upwards [hψ.noncharacteristic hρ, hψ.equation] with z hn he
  exact (completedBoundary_hamiltonian_zero_iff_scalar_normal ν ρ u p ψ z.1 z.2 hn).2 he

end
end NSEGR.Assembly
