import GRAdapter.ScalarCompatibility
import GRAssembly.HodgeTransport

/-! Analytic closure of the literal native spatial differential formulas. -/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly

open Set Filter
open scoped Topology ContDiff

noncomputable section

theorem analyticHodge_scalarSpatialPartial_joint {f : Pressure} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ (fun y : ℝ × Vec => f y.1 y.2) z) (i : Fin 3) :
    AnalyticAt ℝ
      (fun y : ℝ × Vec => fderiv ℝ (f y.1) y.2 (unitVector i)) z := by
  have h := analyticAt_scalarJointPartial hf (0, unitVector i)
  apply h.congr
  filter_upwards [hf.eventually_analyticAt] with y hy
  exact (scalar_spatialDerivative_eq_joint hy i).symm

theorem analyticHodge_gradient_joint {f : Pressure} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ (fun y : ℝ × Vec => f y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => gradient (f y.1) y.2) z := by
  have hall : AnalyticAt ℝ
      (fun y : ℝ × Vec => fun i : Fin 3 => fderiv ℝ (f y.1) y.2 (unitVector i)) z :=
    AnalyticAt.pi (fun i => analyticHodge_scalarSpatialPartial_joint hf i)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.analyticAt _).comp hall

theorem analyticHodge_divergence_joint {w : Velocity} {z : ℝ × Vec}
    (hw : AnalyticAt ℝ (fun y : ℝ × Vec => w y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => divergence (w y.1) y.2) z := by
  apply analyticAt_fin3_sum
  intro i
  exact ((EuclideanSpace.proj i).analyticAt _).comp
    (analyticAt_spatialPartial_joint hw i)

theorem analyticHodge_scalarLaplacian_joint {f : Pressure} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ (fun y : ℝ × Vec => f y.1 y.2) z) :
    AnalyticAt ℝ (fun y : ℝ × Vec => scalarLaplacian (f y.1) y.2) z := by
  apply analyticAt_fin3_sum
  intro i
  exact analyticHodge_scalarSpatialPartial_joint
    (analyticHodge_scalarSpatialPartial_joint hf i) i

/-- The mean is recovered from the actual inverse identity; this helper does
not presume analytic parameter integration. -/
theorem scalarMean_analytic_of_poissonInverse_analytic
    (f : Pressure) {I : Set ℝ} (hI : IsOpen I)
    (hf : AnalyticOnNhd ℝ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ t ∈ I, SpatialPeriodic (f t))
    (hG : AnalyticOnNhd ℝ
      (fun z : ℝ × Vec => poissonInverse (f z.1) z.2) {z | z.1 ∈ I}) :
    AnalyticOnNhd ℝ (fun t => scalarMean (f t)) I := by
  intro t ht
  have hfa : AnalyticAt ℝ (fun s => f s (0 : Vec)) t :=
    (hf (t, 0) ht).curry_left
  have hla : AnalyticAt ℝ
      (fun s => scalarLaplacian (poissonInverse (f s)) (0 : Vec)) t :=
    (analyticHodge_scalarLaplacian_joint (hG (t, 0) ht)).curry_left
  apply (hfa.sub hla).congr
  filter_upwards [hI.mem_nhds ht] with s hs
  have hfs : ContDiff ℝ ∞ (f s) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact ((hf (s, x) hs).curry_right).contDiffAt
  have he := congrFun (scalarLaplacian_poissonInverse (f s) hfs (hp s hs)) (0 : Vec)
  change scalarLaplacian (poissonInverse (f s)) 0 = f s 0 - scalarMean (f s) at he
  change f s 0 - scalarLaplacian (poissonInverse (f s)) 0 = scalarMean (f s)
  linarith

end
end NSEGR.Assembly
