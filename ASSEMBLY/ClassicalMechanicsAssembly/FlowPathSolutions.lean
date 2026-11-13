import ClassicalMechanicsAssembly.FlowTrajectories
import ClassicalMechanicsAssembly.FlowVolterra

/-!
The selected whole-slab trajectories are the unique roots of the concrete
Banach path residual. Both the integral identity and uniqueness are proved;
neither is introduced as an analytic admission.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set Flow
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ} {u : ℝ → E → E} {B K : ℝ≥0}

theorem Flow.SlabODEData.continuousOn_uncurry (h : SlabODEData T u B K) :
    ContinuousOn (Function.uncurry u) (Icc (0 : ℝ) T ×ˢ (univ : Set E)) := by
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K
  · exact fun t ht => (h.lipschitz t ht).lipschitzOnWith
  · exact fun x _ => h.continuous_time x

/-- The supplied velocity as a continuous map on subtype time times space. -/
def flowSlabVelocity (h : SlabODEData T u B K) : C(Icc (0 : ℝ) T × E, E) :=
  ⟨fun z => u z.1 z.2,
    h.continuousOn_uncurry.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, mem_univ _⟩)⟩

@[simp]
theorem flowSlabVelocity_apply (h : SlabODEData T u B K)
    (t : Icc (0 : ℝ) T) (x : E) : flowSlabVelocity h (t, x) = u t x := rfl

theorem trajectory_eq_picard (h : SlabODEData T u B K)
    (s : Icc (0 : ℝ) T) (a : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    trajectory h s a t = ODE.picard u s a (trajectory h s a) t := by
  have hsub : uIcc (s : ℝ) t ⊆ Icc (0 : ℝ) T := uIcc_subset_Icc s.property ht
  have hp := ODE.picard_eq_of_hasDerivAt
    (h.continuousOn_uncurry.mono (Set.prod_mono hsub (Subset.refl _)))
    (fun r hr => (trajectory_hasDerivWithinAt h s a r (hsub hr)).mono hsub)
    (fun _ _ => mem_univ (α := E) _)
  simpa only [trajectory_initial] using hp.symm

/-- Actual selected forward trajectory, viewed in the continuous path Banach space. -/
def selectedFlowPath (h : SlabODEData T u B K) (hT : 0 ≤ T) (a : E) :
    C(Icc (0 : ℝ) T, E) :=
  ⟨fun t => flow h hT t a,
    (trajectory_continuousOn h ⟨0, ⟨le_rfl, hT⟩⟩ a).comp_continuous
      continuous_subtype_val (fun t => t.property)⟩

@[simp]
theorem selectedFlowPath_apply (h : SlabODEData T u B K) (hT : 0 ≤ T)
    (a : E) (t : Icc (0 : ℝ) T) :
    selectedFlowPath h hT a t = flow h hT t a := rfl

theorem pathPrimitive_superposition_eq_integral (h : SlabODEData T u B K)
    (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    flowPathPrimitive hT (flowPathSuperpositionTo (flowSlabVelocity h) γ) t =
      ∫ r in (0 : ℝ)..(t : ℝ), u r (flowPathExtend hT γ r) := by
  rw [flowPathPrimitive_apply]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc (0 : ℝ) T :=
    uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property hr
  simp only [flowPathExtend, projIcc_of_mem hT hrT,
    flowPathSuperpositionTo_apply, flowSlabVelocity_apply]

/-- The actual selected path satisfies the actual Banach integral equation. -/
theorem selectedFlowPath_integral_equation (h : SlabODEData T u B K)
    (hT : 0 ≤ T) (a : E) :
    selectedFlowPath h hT a = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT (flowPathSuperpositionTo (flowSlabVelocity h)
        (selectedFlowPath h hT a)) := by
  ext t
  change flow h hT t a = a +
    flowPathPrimitive hT (flowPathSuperpositionTo (flowSlabVelocity h)
      (selectedFlowPath h hT a)) t
  rw [pathPrimitive_superposition_eq_integral]
  have hp := trajectory_eq_picard h ⟨0, ⟨le_rfl, hT⟩⟩ a t t.property
  change flow h hT t a = a + ∫ r in (0 : ℝ)..(t : ℝ), u r (flow h hT r a) at hp
  rw [hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc (0 : ℝ) T :=
    uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property hr
  rw [flowPathExtend_of_mem hT _ r hrT]
  rfl

/-- Every root of the actual path integral equation is the selected ODE solution. -/
theorem selectedFlowPath_integral_unique (h : SlabODEData T u B K)
    (hT : 0 ≤ T) (a : E) (γ : C(Icc (0 : ℝ) T, E))
    (hγ : γ = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT (flowPathSuperpositionTo (flowSlabVelocity h) γ)) :
    γ = selectedFlowPath h hT a := by
  let f : ℝ → E := flowPathExtend hT γ
  have hpic : ∀ t ∈ Icc (0 : ℝ) T, f t = ODE.picard u 0 a f t := by
    intro t ht
    have he := congrArg (fun k : C(Icc (0 : ℝ) T, E) => k ⟨t, ht⟩) hγ
    change γ ⟨t, ht⟩ = a +
      flowPathPrimitive hT (flowPathSuperpositionTo (flowSlabVelocity h) γ) ⟨t, ht⟩ at he
    rw [pathPrimitive_superposition_eq_integral] at he
    simpa only [f, flowPathExtend_of_mem hT γ t ht, ODE.picard_apply] using he
  have hder : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (u t (f t)) (Icc 0 T) t := by
    intro t ht
    exact (ODE.hasDerivWithinAt_picard_Icc ⟨le_rfl, hT⟩ h.continuousOn_uncurry
      (flowPathExtend_continuous hT γ).continuousOn (fun _ _ => mem_univ _) a ht).congr_of_mem
        hpic ht
  have hinit : f 0 = a := by
    simpa only [ODE.picard_apply₀] using hpic 0 ⟨le_rfl, hT⟩
  have heq := solution_unique h ⟨0, ⟨le_rfl, hT⟩⟩ hder
    (flow_hasDerivWithinAt h hT a) (hinit.trans (flow_initial h hT a).symm)
  ext t
  simpa only [f, flowPathExtend_of_mem hT γ t t.property, selectedFlowPath_apply] using
    heq t.property

end

end ClassicalMechanicsAssembly
