import GRAdapter.ScalarCK

/-!
# Compatibility of the concrete first-order scalar CK system

The transported gradient variables are identified with the actual spatial
gradient of the potential, as germs. No compatibility assumption is added.
The proof uses symmetry of the analytic second Frechet derivative and the
one-dimensional zero-derivative theorem on a product neighborhood.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace NSEGR
noncomputable section

def scalarJointPartial (f : ℝ × Vec → ℝ) (d : ℝ × Vec) (z : ℝ × Vec) : ℝ :=
  fderiv ℝ f z d

theorem analyticAt_scalarJointPartial {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (d : ℝ × Vec) :
    AnalyticAt ℝ (scalarJointPartial f d) z := by
  let ev : ((ℝ × Vec) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ d
  exact (ev.analyticAt _).comp hf.fderiv

theorem scalarJointPartial_commute {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (v w : ℝ × Vec) :
    scalarJointPartial (scalarJointPartial f v) w z =
      scalarJointPartial (scalarJointPartial f w) v z := by
  have heval (d e : ℝ × Vec) :
      scalarJointPartial (scalarJointPartial f d) e z =
        fderiv ℝ (fderiv ℝ f) z e d := by
    let ev : ((ℝ × Vec) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ d
    have h := ev.hasFDerivAt.comp z hf.fderiv.differentiableAt.hasFDerivAt
    exact congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L e) h.fderiv
  rw [heval, heval]
  exact (hf.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega w v

theorem scalar_timeDerivative_eq_joint {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) :
    deriv (fun t : ℝ => f (t, z.2)) z.1 = scalarJointPartial f (1, 0) z := by
  have hm : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Vec)) z.1 :=
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))
  have h := hf.differentiableAt.hasFDerivAt.comp z.1 hm
  simpa only [scalarJointPartial, Function.comp_def, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using h.hasDerivAt.deriv

theorem scalar_spatialDerivative_eq_joint {f : ℝ × Vec → ℝ} {z : ℝ × Vec}
    (hf : AnalyticAt ℝ f z) (i : Fin 3) :
    fderiv ℝ (fun x : Vec => f (z.1, x)) z.2 (unitVector i) =
      scalarJointPartial f (0, unitVector i) z := by
  have hm : HasFDerivAt (fun x : Vec => (z.1, x))
      ((0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec)) z.2 :=
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))
  have h := hf.differentiableAt.hasFDerivAt.comp z.2 hm
  simpa only [scalarJointPartial, Function.comp_def, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using
    congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) h.fderiv

/-- Zero time derivative and zero initial germ imply a zero spacetime germ. -/
theorem analytic_zero_transport_germ {f : ℝ × Vec → ℝ} {t0 : ℝ} {x0 : Vec}
    (hf : AnalyticAt ℝ f (t0, x0))
    (hdt : ∀ᶠ z in 𝓝 (t0, x0), deriv (fun t : ℝ => f (t, z.2)) z.1 = 0)
    (h0 : ∀ᶠ x in 𝓝 x0, f (t0, x) = 0) :
    ∀ᶠ z in 𝓝 (t0, x0), f z = 0 := by
  obtain ⟨U, hU, V, hV, hUV⟩ :=
    mem_nhds_prod_iff.mp (hf.eventually_analyticAt.and hdt)
  obtain ⟨a, b, ht0, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  have ht : Ioo a b ∈ 𝓝 t0 := Ioo_mem_nhds ht0.1 ht0.2
  filter_upwards [ht.prodMk_nhds (hV.and h0)] with z hz
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => f (t, z.2)) (Ioo a b) := by
    intro t ht'
    exact (hUV ⟨hab ht', hz.2.1⟩).1.curry_left.differentiableAt.differentiableWithinAt
  have hzero : (Ioo a b).EqOn (deriv (fun t : ℝ => f (t, z.2))) 0 := by
    intro t ht'
    exact (hUV ⟨hab ht', hz.2.1⟩).2
  exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hz.1 ht0).trans
    hz.2.2

theorem scalarCK_coordinate_jointDerivative {W : ℝ × Vec → ScalarCKState}
    {z : ℝ × Vec} (hW : AnalyticAt ℝ W z) (k : Fin 5) (d : ℝ × Vec) :
    scalarJointPartial (fun y => W y k) d z = fderiv ℝ W z d k := by
  let ev : ScalarCKState →L[ℝ] ℝ := EuclideanSpace.proj k
  have h := ev.hasFDerivAt.comp z hW.differentiableAt.hasFDerivAt
  exact congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L d) h.fderiv

theorem scalarCK_spatial_coordinate_derivative {W : ℝ × Vec → ScalarCKState}
    {z : ℝ × Vec} (hW : AnalyticAt ℝ W z) (k : Fin 5) (i : Fin 3) :
    fderiv ℝ (fun x => W (z.1, x)) z.2 (unitVector i) k =
      scalarJointPartial (fun y => W y k) (0, unitVector i) z := by
  have hm : HasFDerivAt (fun x : Vec => (z.1, x))
      ((0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec)) z.2 :=
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))
  have h := hW.differentiableAt.hasFDerivAt.comp z.2 hm
  rw [scalarCK_coordinate_jointDerivative hW k (0, unitVector i)]
  simpa only [Function.comp_def, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using
    congrArg (fun L : Vec →L[ℝ] ScalarCKState => L (unitVector i) k) h.fderiv

/-- The two transport identities are consequences of the concrete CK system. -/
theorem scalarCK_solution_transport
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) (i : Fin 3) :
    ∀ᶠ z in 𝓝 (t0, x0),
      scalarJointPartial (fun y => W y 0) (1, 0) z = W z 1 ∧
      scalarJointPartial (fun y => W y (scalarCKGradientIndex i)) (1, 0) z =
        scalarJointPartial (fun y => W y 1) (0, unitVector i) z := by
  filter_upwards [hW.analytic.eventually_analyticAt, hW.equation] with z ha he
  have hm : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Vec)) z.1 :=
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))
  have ht := ha.differentiableAt.hasFDerivAt.comp z.1 hm
  have ht' : deriv (fun t : ℝ => W (t, z.2)) z.1 = fderiv ℝ W z (1, 0) := by
    simpa only [Function.comp_def, id_eq,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using ht.hasDerivAt.deriv
  constructor
  · rw [scalarCK_coordinate_jointDerivative ha, ← ht', he]
    exact scalarCKRHS_potential ν ρ u p _
  · rw [scalarCK_coordinate_jointDerivative ha, ← ht', he, scalarCKRHS_gradient]
    exact scalarCK_spatial_coordinate_derivative ha 1 i

/-- The transported variable equals the actual spatial gradient component.
Only the actual zero-data solution of the fixed concrete system is assumed. -/
theorem scalarCK_gradient_compatibility
    {ν ρ t0 : ℝ} {u : Velocity} {p : Pressure} {x0 : Vec}
    {W : ℝ × Vec → ScalarCKState}
    (hW : LiteratureCKSolution (scalarCKRHS ν ρ u p)
      (fun _ : Vec => (0 : ScalarCKState)) t0 x0 W) (i : Fin 3) :
    ∀ᶠ z in 𝓝 (t0, x0),
      W z (scalarCKGradientIndex i) =
        gradient (fun x => W (z.1, x) 0) z.2 i := by
  let f : ℝ × Vec → ℝ := fun y => W y 0
  let g : ℝ × Vec → ℝ := fun y => W y (scalarCKGradientIndex i)
  let v : ℝ × Vec → ℝ := fun y => W y 1
  let d : ℝ × Vec := (0, unitVector i)
  let ef : ScalarCKState →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 5)
  let eg : ScalarCKState →L[ℝ] ℝ := EuclideanSpace.proj (scalarCKGradientIndex i)
  have hf : AnalyticAt ℝ f (t0, x0) := (ef.analyticAt _).comp hW.analytic
  have hg : AnalyticAt ℝ g (t0, x0) := (eg.analyticAt _).comp hW.analytic
  have hdf := analyticAt_scalarJointPartial hf d
  have he : AnalyticAt ℝ (fun z => g z - scalarJointPartial f d z) (t0, x0) := by
    simpa only [Pi.sub_def] using hg.sub hdf
  have heq := scalarCK_solution_transport hW i
  have hfv : scalarJointPartial f (1, 0) =ᶠ[𝓝 (t0, x0)] v :=
    heq.mono (fun _ h => h.1)
  have hdt : ∀ᶠ z in 𝓝 (t0, x0),
      deriv (fun t : ℝ => g (t, z.2) - scalarJointPartial f d (t, z.2)) z.1 = 0 := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt,
      hdf.eventually_analyticAt, heq, hfv.fderiv] with z hfa hga hdfa hz hd
    rw [deriv_sub hga.curry_left.differentiableAt hdfa.curry_left.differentiableAt]
    rw [scalar_timeDerivative_eq_joint hga, scalar_timeDerivative_eq_joint hdfa]
    rw [scalarJointPartial_commute hfa d (1, 0)]
    have hd' := congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L d) hd
    change scalarJointPartial (scalarJointPartial f (1, 0)) d z =
      scalarJointPartial v d z at hd'
    rw [hd', hz.2]
    exact sub_self _
  have h0f : (fun x : Vec => f (t0, x)) =ᶠ[𝓝 x0] (fun _ => (0 : ℝ)) := by
    filter_upwards [hW.initial] with x hx
    exact congrArg (fun a : ScalarCKState => a 0) hx
  have hslice : ∀ᶠ x in 𝓝 x0, AnalyticAt ℝ f (t0, x) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
      hf.eventually_analyticAt
  have h0 : ∀ᶠ x in 𝓝 x0, g (t0, x) - scalarJointPartial f d (t0, x) = 0 := by
    filter_upwards [hW.initial, h0f.fderiv, hslice] with x hx hdx hax
    have hgv : g (t0, x) = 0 := congrArg
      (fun a : ScalarCKState => a (scalarCKGradientIndex i)) hx
    have hdv : scalarJointPartial f d (t0, x) = 0 := by
      rw [← scalar_spatialDerivative_eq_joint hax i]
      rw [hdx]
      simp
    rw [hgv, hdv, sub_self]
  have herror := analytic_zero_transport_germ he hdt h0
  filter_upwards [herror, hf.eventually_analyticAt] with z hz hfa
  have hz' : g z = scalarJointPartial f d z := sub_eq_zero.mp hz
  change g z = fderiv ℝ (fun x : Vec => f (z.1, x)) z.2 (unitVector i)
  rw [scalar_spatialDerivative_eq_joint hfa i]
  exact hz'

end
end NSEGR
