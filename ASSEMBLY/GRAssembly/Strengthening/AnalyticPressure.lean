import GRAssembly.Strengthening.PressureIdentification
import GRAssembly.AnalyticHodge

/-!
G16: positive-time analyticity of the actual origin-normalized pressure is
derived from the actual NSE and positive-time velocity analyticity. The
quadratic source, Poisson inverse and normalization are the native formulas.
The separate G06--G15 velocity-smoothing obligation remains explicit.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff BigOperators

namespace NSEGR.Strengthening
noncomputable section

theorem analyticAt_velocityOuter_divergence_joint
    {u : Velocity} {z : ℝ × Vec}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) z) :
    AnalyticAt ℝ
      (fun y : ℝ × Vec => tensorDivergence (fun x => velocityOuter (u y.1 x)) y.2) z := by
  apply Assembly.analyticAt_vec_of_components
  intro i
  have hc (j : Fin 3) : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2 j) z := by
    let pr : Vec →L[ℝ] ℝ := EuclideanSpace.proj j
    change AnalyticAt ℝ (fun y : ℝ × Vec => pr (u y.1 y.2)) z
    exact (pr.analyticAt (u z.1 z.2)).comp_of_eq hu rfl
  have hs : AnalyticAt ℝ
      (fun y : ℝ × Vec => ∑ j : Fin 3,
        fderiv ℝ (fun x : Vec => u y.1 x i * u y.1 x j) y.2 (unitVector j)) z := by
    apply analyticAt_fin3_sum
    intro j
    exact Assembly.analyticHodge_scalarSpatialPartial_joint
      (f := fun t x => u t x i * u t x j) ((hc i).mul (hc j)) j
  simpa only [tensorDivergence, velocityOuter, PiLp.toLp_apply] using hs

theorem analyticAt_quadraticPressureSource_joint
    {u : Velocity} {z : ℝ × Vec}
    (hu : AnalyticAt ℝ (fun y : ℝ × Vec => u y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => quadraticPressureSource (u y.1) y.2) z := by
  exact (Assembly.analyticHodge_divergence_joint
    (w := fun t => tensorDivergence (fun x => velocityOuter (u t x)))
    (analyticAt_velocityOuter_divergence_joint hu)).neg

theorem quadraticPressureSource_periodic {v : Field}
    (hv : SpatialPeriodic v) : SpatialPeriodic (quadraticPressureSource v) := by
  have htransport : SpatialPeriodic (tensorDivergence (fun x => velocityOuter (v x))) := by
    intro x j
    apply PiLp.ext
    intro i
    change (∑ k : Fin 3,
      fderiv ℝ (fun y : Vec => v y i * v y k) (x + unitVector j) (unitVector k)) =
      ∑ k : Fin 3, fderiv ℝ (fun y : Vec => v y i * v y k) x (unitVector k)
    apply Finset.sum_congr rfl
    intro k _
    have hprod : SpatialPeriodic (fun y : Vec => v y i * v y k) := by
      intro y l
      change v (y + unitVector l) i * v (y + unitVector l) k = v y i * v y k
      rw [hv y l]
    exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector k))
      (fderiv_periodic hprod x j)
  intro x j
  exact congrArg Neg.neg (divergence_periodic htransport x j)

theorem originNormalize_analytic_on_open_slab
    {p : Pressure} {I : Set ℝ} (_hI : IsOpen I)
    (hp : AnalyticOnNhd ℝ (fun z : ℝ × Vec => p z.1 z.2) {z | z.1 ∈ I}) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => originNormalize p z.1 z.2) {z | z.1 ∈ I} := by
  intro z hz
  have hmap : AnalyticAt ℝ (fun w : ℝ × Vec => (w.1, (0 : Vec))) z :=
    analyticAt_fst.prod analyticAt_const
  have hp0 : AnalyticAt ℝ (fun w : ℝ × Vec => p w.1 0) z :=
    (hp (z.1, 0) hz).comp_of_eq hmap rfl
  change AnalyticAt ℝ (fun w : ℝ × Vec => p w.1 w.2 - p w.1 0) z
  exact (hp z hz).sub hp0

theorem normalizedQuadraticPressure_joint_analytic_on_open_slab
    {u : Velocity} {I : Set ℝ} (hI : IsOpen I)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) {z | z.1 ∈ I})
    (hper : ∀ t ∈ I, SpatialPeriodic (u t)) :
    AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => normalizedQuadraticPressure (u z.1) z.2) {z | z.1 ∈ I} := by
  have hsource : AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => quadraticPressureSource (u z.1) z.2) {z | z.1 ∈ I} :=
    fun z hz => analyticAt_quadraticPressureSource_joint (u := u) (z := z) (hu z hz)
  have hsourceper : ∀ t ∈ I, SpatialPeriodic (quadraticPressureSource (u t)) :=
    fun t ht => quadraticPressureSource_periodic (v := u t) (hper t ht)
  have hpi : AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => poissonInverse (quadraticPressureSource (u z.1)) z.2)
      {z | z.1 ∈ I} :=
    Assembly.poissonInverse_joint_analytic_on_open_slab
      (fun t => quadraticPressureSource (u t)) (I := I) hI hsource hsourceper
  have hnormalized := originNormalize_analytic_on_open_slab
    (p := fun t => poissonInverse (quadraticPressureSource (u t))) (I := I) hI hpi
  simpa only [originNormalize, normalizedQuadraticPressure, quadraticPoissonPressure] using hnormalized

theorem nssolution_originNormalize_positive_analytic
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => originNormalize p z.1 z.2)
      positiveSpacetime := by
  have hq : AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => normalizedQuadraticPressure (u z.1) z.2) positiveSpacetime :=
    normalizedQuadraticPressure_joint_analytic_on_open_slab
      (u := u) (I := Ioi (0 : ℝ)) isOpen_Ioi hu
      (fun t ht => h.velocity_periodic t ht.le)
  have hopen : IsOpen positiveSpacetime := isOpen_lt continuous_const continuous_fst
  intro z hz
  apply (hq z hz).congr
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact congrFun (nssolution_normalized_pressure_eq_quadraticPoisson h hw.le).symm w.2

theorem positiveAnalyticNSE_of_nssolution_velocity_analytic
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime) :
    PositiveAnalyticNSE ν u (originNormalize p) :=
  positiveAnalyticNSE_of_nssolution (nssolution_originNormalize h) hu
    (nssolution_originNormalize_positive_analytic h hu)

end
end NSEGR.Strengthening
