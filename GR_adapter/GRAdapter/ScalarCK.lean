import GRAdapter.LiteratureInputs
import GRAdapter.ScalarAnalytic

/-!
# Native first-order scalar CK specialization

The five unknowns are `(psi, v, z_0, z_1, z_2)`. The actual RHS is
`(v, scalarJetRHS rho u A (D_x z) (D_x v), D_x v)`, with the native
NSE source `A`. Analyticity at the zero initial jet is proved from joint
analyticity of `u,p` and `rho != 0`; it is not a new hypothesis.

Only LI01 supplies existence and uniqueness. The output is the concrete
five-component analytic germ. Identifying `z = grad psi`, reconstructing
the scalar second derivative, periodic gluing, and the CompletedBoundary
record are separate remaining steps.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace NSEGR
noncomputable section

/-- Joint analyticity of the literal spatial derivative of a velocity. -/
theorem analyticAt_spatialPartial_joint {u : Velocity} {z : ℝ × Vec}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) z) (i : Fin 3) :
    AnalyticAt ℝ (fun y : ℝ × Vec => spatialPartial (u y.1) i y.2) z := by
  have htotal : AnalyticAt ℝ
      (fun y : ℝ × Vec =>
        fderiv ℝ (fun w : ℝ × Vec => u w.1 w.2) y (0, unitVector i)) z :=
    ((ContinuousLinearMap.apply ℝ Vec (0, unitVector i)).analyticAt _).comp hu.fderiv
  apply htotal.congr
  filter_upwards [hu.eventually_analyticAt] with y hy
  have hslice := hy.differentiableAt.hasFDerivAt.comp
    ((hasFDerivAt_const y.1 y.2).prodMk (hasFDerivAt_id y.2))
  have heq := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i)) hslice.fderiv
  simpa only [spatialPartial, Function.comp_def, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] using heq.symm

/-- Every entry of the actual NSE spatial source is jointly analytic. -/
theorem analyticAt_nseSpatialSource3_components
    {ν : ℝ} {u : Velocity} {p : Pressure} {z : ℝ × Vec}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) z)
    (hp : AnalyticAt ℝ (fun y : ℝ × Vec => p y.1 y.2) z) (i j : Fin 3) :
    AnalyticAt ℝ (fun y : ℝ × Vec => nseSpatialSource3 ν u p y.1 y.2 i j) z := by
  have hui := ((EuclideanSpace.proj i).analyticAt _).comp hu
  have huj := ((EuclideanSpace.proj j).analyticAt _).comp hu
  have hij := ((EuclideanSpace.proj j).analyticAt _).comp
    (analyticAt_spatialPartial_joint hu i)
  have hji := ((EuclideanSpace.proj i).analyticAt _).comp
    (analyticAt_spatialPartial_joint hu j)
  have hc : AnalyticAt ℝ (fun _ : ℝ × Vec => identity3 i j) z := analyticAt_const
  have hν : AnalyticAt ℝ (fun _ : ℝ × Vec => ν) z := analyticAt_const
  simpa only [nseSpatialSource3, strain, Function.comp_def,
    Pi.mul_def, Pi.add_def, Pi.sub_def] using
    ((hui.mul huj).add (hp.mul hc)).sub (hν.mul (hij.add hji))

abbrev ScalarCKState := LiteratureSpace 5
abbrev ScalarCKJet := LiteratureCKJet 3 5

def scalarCKGradientIndex (i : Fin 3) : Fin 5 := i.succ.succ

/-- `Q_ij = partial_i z_j` in the first-order jet. -/
def scalarCKSpatialJet (J : ScalarCKJet) : Tensor3 :=
  fun i j => J.2.2 (unitVector i) (scalarCKGradientIndex j)

/-- `b_i = partial_i v` in the first-order jet. -/
def scalarCKMixedJet (J : ScalarCKJet) : Fin 3 → ℝ :=
  fun i => J.2.2 (unitVector i) 1

/-- The literal five-component first-order CK RHS. -/
def scalarCKRHS (ν ρ : ℝ) (u : Velocity) (p : Pressure) : LiteratureCKRHS 3 5 :=
  fun J => WithLp.toLp 2 (Fin.cases (J.2.1 1)
    (Fin.cases
      (scalarJetRHS ρ (fun i => u J.1.1 J.1.2 i)
        (nseSpatialSource3 ν u p J.1.1 J.1.2)
        (scalarCKSpatialJet J) (scalarCKMixedJet J))
      (scalarCKMixedJet J)))

theorem scalarCKRHS_potential (ν ρ : ℝ) (u : Velocity) (p : Pressure)
    (J : ScalarCKJet) : scalarCKRHS ν ρ u p J 0 = J.2.1 1 := rfl

theorem scalarCKRHS_time (ν ρ : ℝ) (u : Velocity) (p : Pressure)
    (J : ScalarCKJet) : scalarCKRHS ν ρ u p J 1 =
      scalarJetRHS ρ (fun i => u J.1.1 J.1.2 i)
        (nseSpatialSource3 ν u p J.1.1 J.1.2)
        (scalarCKSpatialJet J) (scalarCKMixedJet J) := rfl

theorem scalarCKRHS_gradient (ν ρ : ℝ) (u : Velocity) (p : Pressure)
    (J : ScalarCKJet) (i : Fin 3) :
    scalarCKRHS ν ρ u p J (scalarCKGradientIndex i) = J.2.2 (unitVector i) 1 := rfl

theorem analyticAt_scalarCKJet_entry (J : ScalarCKJet) (i : Fin 3) (j : Fin 5) :
    AnalyticAt ℝ (fun Y : ScalarCKJet => Y.2.2 (unitVector i) j) J := by
  have hd : AnalyticAt ℝ
      (fun Y : ScalarCKJet => Y.2.2) J := analyticAt_snd.comp analyticAt_snd
  exact ((EuclideanSpace.proj j).analyticAt _).comp
    (((ContinuousLinearMap.apply ℝ ScalarCKState (unitVector i)).analyticAt _).comp hd)

/-- The actual five-component RHS is analytic at every noncharacteristic jet. -/
theorem analyticAt_scalarCKRHS
    {ν ρ : ℝ} {u : Velocity} {p : Pressure} {J : ScalarCKJet}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) J.1)
    (hp : AnalyticAt ℝ (fun y : ℝ × Vec => p y.1 y.2) J.1)
    (hden : ρ + trace3 (scalarCKSpatialJet J) ≠ 0) :
    AnalyticAt ℝ (scalarCKRHS ν ρ u p) J := by
  have huJ : ∀ i : Fin 3,
      AnalyticAt ℝ (fun Y : ScalarCKJet => u Y.1.1 Y.1.2 i) J := by
    intro i
    exact (((EuclideanSpace.proj i).analyticAt _).comp hu).comp analyticAt_fst
  have hAJ : ∀ i j : Fin 3,
      AnalyticAt ℝ (fun Y : ScalarCKJet => nseSpatialSource3 ν u p Y.1.1 Y.1.2 i j) J := by
    intro i j
    exact (analyticAt_nseSpatialSource3_components hu hp i j).comp analyticAt_fst
  have hQ : ∀ i j : Fin 3,
      AnalyticAt ℝ (fun Y : ScalarCKJet => scalarCKSpatialJet Y i j) J := by
    intro i j
    exact analyticAt_scalarCKJet_entry J i (scalarCKGradientIndex j)
  have hb : ∀ i : Fin 3,
      AnalyticAt ℝ (fun Y : ScalarCKJet => scalarCKMixedJet Y i) J := by
    intro i
    exact analyticAt_scalarCKJet_entry J i 1
  have hF := analyticAt_scalarJetRHS_components
    (show AnalyticAt ℝ (fun _ : ScalarCKJet => ρ) J from analyticAt_const)
    huJ hAJ hQ hb hden
  have hv : AnalyticAt ℝ (fun Y : ScalarCKJet => Y.2.1 1) J :=
    ((EuclideanSpace.proj (1 : Fin 5)).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd)
  have hall : AnalyticAt ℝ
      (fun Y : ScalarCKJet => Fin.cases (Y.2.1 1)
        (Fin.cases
          (scalarJetRHS ρ (fun i => u Y.1.1 Y.1.2 i)
            (nseSpatialSource3 ν u p Y.1.1 Y.1.2)
            (scalarCKSpatialJet Y) (scalarCKMixedJet Y))
          (scalarCKMixedJet Y))) J := by
    apply AnalyticAt.pi
    intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · exact hv
    · refine Fin.cases ?_ (fun i => ?_) l
      · exact hF
      · exact hb i
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).symm.analyticAt _).comp hall

theorem scalarCK_zero_initial_noncharacteristic {ρ t0 : ℝ} (hρ : ρ ≠ 0) (x0 : Vec) :
    ρ + trace3 (scalarCKSpatialJet
      (LiteratureCKInitialJet t0 x0 (fun _ : Vec => (0 : ScalarCKState)))) ≠ 0 := by
  simpa [LiteratureCKInitialJet, scalarCKSpatialJet, trace3] using hρ

/-- LI01 instantiated at the concrete NSE-dependent scalar system and zero data.
No analytic-RHS, solution, or completion premise is added to LI01. -/
theorem scalarCK_exists_unique_firstOrder
    (input : LiteratureAnalyticCKInput)
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    (hρ : ρ ≠ 0) (hpair : AnalyticPeriodicPair t0 δ u p) (x0 : Vec) :
    ∃ W : ℝ × Vec → ScalarCKState,
      LiteratureCKSolution (scalarCKRHS ν ρ u p)
        (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W ∧
      ∀ V : ℝ × Vec → ScalarCKState,
        LiteratureCKSolution (scalarCKRHS ν ρ u p)
          (fun _ : Vec => (0 : ScalarCKState)) t0 x0 V →
        W =ᶠ[𝓝 (t0, x0)] V := by
  have hbase : (t0, x0) ∈ spacetimeSlab t0 δ := by
    constructor <;> linarith [hpair.radius_pos]
  apply input.exists_unique 3 5 (by norm_num) (by norm_num)
    (scalarCKRHS ν ρ u p) (fun _ : Vec => (0 : ScalarCKState)) t0 x0
    analyticAt_const
  exact analyticAt_scalarCKRHS
    (hpair.velocity_analytic (t0, x0) hbase)
    (hpair.pressure_analytic (t0, x0) hbase)
    (scalarCK_zero_initial_noncharacteristic hρ x0)

end
end NSEGR
