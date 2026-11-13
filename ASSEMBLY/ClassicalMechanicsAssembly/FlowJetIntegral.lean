import ClassicalMechanicsAssembly.FlowImplicit
import ClassicalMechanicsAssembly.FlowPathJets
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Integral identities for the actual label jets

The path equation is differentiated in the Banach path space. Evaluation and
the actual primitive are continuous linear maps. Consequently, every actual
label jet satisfies its differentiated integral equation before joint time
smoothness is established.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff NNReal

noncomputable section

/-- Postcomposition by the actual primitive commutes with evaluation of all
multilinear coordinates, giving an integral in the tensor space itself. -/
theorem flow_primitive_evaluated_jet {T : ℝ} (hT : 0 ≤ T)
    {H : Vec → C(Icc (0 : ℝ) T, Vec)} (hH : ContDiff ℝ ∞ H)
    (r : ℕ) (t : Icc (0 : ℝ) T) (a : Vec) :
    ((ContinuousMap.evalCLM ℝ t).comp (flowPathPrimitive hT)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ r H a) =
      ∫ s in (0 : ℝ)..(t : ℝ), evaluatedFlowJet H r (projIcc 0 T hT s) a := by
  have hproj : Continuous (fun s : ℝ => (projIcc 0 T hT s, a)) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := T) (h := hT)).prodMk continuous_const
  have hc : Continuous (fun s : ℝ => evaluatedFlowJet H r (projIcc 0 T hT s) a) :=
    (evaluatedFlowJet_continuous hH r).comp hproj
  have hi := hc.intervalIntegrable 0 (t : ℝ)
  ext m
  have hm := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec) Vec m)
    .intervalIntegral_comp_comm hi
  change flowPathPrimitive hT (iteratedFDeriv ℝ r H a m) t =
    (∫ s in (0 : ℝ)..(t : ℝ), evaluatedFlowJet H r (projIcc 0 T hT s) a) m
  rw [flowPathPrimitive_apply]
  calc
    _ = ∫ s in (0 : ℝ)..(t : ℝ),
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec) Vec m)
          (evaluatedFlowJet H r (projIcc 0 T hT s) a) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rfl
    _ = _ := hm

/-- The actual evaluated jets satisfy the differentiated Banach integral equation. -/
theorem evaluatedFlowJet_integral_of_path_equation {T : ℝ} (hT : 0 ≤ T)
    {Γ H : Vec → C(Icc (0 : ℝ) T, Vec)}
    (hΓ : ContDiff ℝ ∞ Γ) (hH : ContDiff ℝ ∞ H)
    (hroot : ∀ a, Γ a = ContinuousMap.const (Icc (0 : ℝ) T) a + flowPathPrimitive hT (H a))
    (r : ℕ) (t : Icc (0 : ℝ) T) (a : Vec) :
    evaluatedFlowJet Γ r t a = evaluatedFlowJet Γ r ⟨0, ⟨le_rfl, hT⟩⟩ a +
      ∫ s in (0 : ℝ)..(t : ℝ), evaluatedFlowJet H r (projIcc 0 T hT s) a := by
  let t0 : Icc (0 : ℝ) T := ⟨0, ⟨le_rfl, hT⟩⟩
  let e0 := ContinuousMap.evalCLM ℝ (M := Vec) t0
  let et := ContinuousMap.evalCLM ℝ (M := Vec) t
  let V := flowPathPrimitive (E := Vec) hT
  have hr : (r : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl r
  have hzero : ∀ b : Vec, Γ b t0 = b := by
    intro b
    have he := congrArg (fun p : C(Icc (0 : ℝ) T, Vec) => p t0) (hroot b)
    simpa [t0, flowPathPrimitive_apply] using he
  have heq : et ∘ Γ = e0 ∘ Γ + (et.comp V) ∘ H := by
    funext b
    have he := congrArg (fun p : C(Icc (0 : ℝ) T, Vec) => p t) (hroot b)
    change Γ b t = Γ b t0 + flowPathPrimitive hT (H b) t
    rw [hzero b]
    exact he
  have hd := congrArg (fun f : Vec → Vec => iteratedFDeriv ℝ r f a) heq
  rw [iteratedFDeriv_add_apply (i := r)
    ((e0.contDiff.comp hΓ).of_le hr).contDiffAt
    (((et.comp V).contDiff.comp hH).of_le hr).contDiffAt] at hd
  rw [et.iteratedFDeriv_comp_left (i := r) hΓ.contDiffAt hr,
    e0.iteratedFDeriv_comp_left (i := r) hΓ.contDiffAt hr,
    (et.comp V).iteratedFDeriv_comp_left (i := r) hH.contDiffAt hr] at hd
  exact hd.trans (congrArg (fun J => evaluatedFlowJet Γ r t0 a + J)
    (flow_primitive_evaluated_jet hT hH r t a))

/-- Identification with ordinary spatial derivatives of an arbitrary total
representative that agrees with the continuous path family on the slab. -/
theorem flow_labelJet_eq_evaluated {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    (η : Velocity)
    (hrep : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec), η t a = Γ a ⟨t, ht⟩)
    (r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    iteratedFDeriv ℝ r (η t) a = evaluatedFlowJet Γ r ⟨t, ht⟩ a := by
  have heq : η t = (ContinuousMap.evalCLM ℝ ⟨t, ht⟩) ∘ Γ := funext (hrep t ht)
  rw [heq]
  exact (ContinuousMap.evalCLM ℝ ⟨t, ht⟩).iteratedFDeriv_comp_left (i := r)
    hΓ.contDiffAt (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)

/-- Every actual label derivative of an integral-curve family satisfies the
literal differentiated time-integral equation, including the boundary times. -/
theorem flow_labelJet_integral_of_path_equation {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    (hroot : ∀ a, Γ a = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT.le (flowPathSuperpositionTo (flowVelocityMap hu) (Γ a)))
    (η : Velocity)
    (hrep : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec), η t a = Γ a ⟨t, ht⟩)
    (r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    iteratedFDeriv ℝ r (η t) a = iteratedFDeriv ℝ r (η 0) a +
      ∫ s in (0 : ℝ)..t, iteratedFDeriv ℝ r (fun b => u s (η s b)) a := by
  let H := flowPathSuperpositionTo (flowVelocityMap hu) ∘ Γ
  have hH : ContDiff ℝ ∞ H := (periodic_velocity_superposition_contDiff hT hu hp).comp hΓ
  have hforce : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T),
      iteratedFDeriv ℝ r (fun b => u s (η s b)) a =
        evaluatedFlowJet H r ⟨s, hs⟩ a := by
    intro s hs
    apply flow_labelJet_eq_evaluated hH (fun s b => u s (η s b))
    intro q hq b
    change u q (η q b) = u q (Γ b ⟨q, hq⟩)
    rw [hrep q hq b]
  rw [flow_labelJet_eq_evaluated hΓ η hrep r t ht a,
    flow_labelJet_eq_evaluated hΓ η hrep r 0 ⟨le_rfl, hT.le⟩ a]
  rw [evaluatedFlowJet_integral_of_path_equation hT.le hΓ hH hroot r ⟨t, ht⟩ a]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ∈ Icc (0 : ℝ) T := uIcc_subset_Icc ⟨le_rfl, hT.le⟩ ht hs
  change evaluatedFlowJet H r (projIcc 0 T hT.le s) a =
    iteratedFDeriv ℝ r (fun b => u s (η s b)) a
  rw [projIcc_of_mem hT.le hsT]
  exact (hforce s hsT).symm

/-- The actual selected periodic ODE flow satisfies every differentiated
integral equation, with no joint-flow smoothness premise. -/
theorem selectedFlow_labelJet_integral {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    {B K : ℝ≥0} (h : Flow.SlabODEData T u B K)
    (r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    iteratedFDeriv ℝ r (Flow.flow h hT.le t) a =
      iteratedFDeriv ℝ r (Flow.flow h hT.le 0) a +
      ∫ s in (0 : ℝ)..t,
        iteratedFDeriv ℝ r (fun b => u s (Flow.flow h hT.le s b)) a := by
  have heq : flowVelocityMap hu = flowSlabVelocity h := by ext z; rfl
  apply flow_labelJet_integral_of_path_equation hT hu hp
    (selectedFlowPath_contDiff hT hu hp h) _ (Flow.flow h hT.le) _ r t ht a
  · intro b
    rw [heq]
    exact selectedFlowPath_integral_equation h hT.le b
  · intro s hs b
    rfl

end

end ClassicalMechanicsAssembly
