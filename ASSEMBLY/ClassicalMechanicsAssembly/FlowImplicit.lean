import ClassicalMechanicsAssembly.FlowVolterra
import ClassicalMechanicsAssembly.FlowSpatialJets
import ClassicalMechanicsAssembly.FlowPathSolutions

/-!
# The actual integral residual and its smooth solution branch

This module fixes the residual as `γ - const a - V (N γ)`. Its partial
derivative is computed, and the concrete Volterra inverse is used. The
remaining inputs of the path theorem are exposed as actual superposition
calculus, the actual integral equation, and uniqueness of its solutions.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set
open scoped Topology ContDiff NNReal

noncomputable section

section Residual

variable {E B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The fixed integral-equation residual. -/
def flowIntegralResidual (c : E →L[ℝ] B) (V : B →L[ℝ] B) (N : B → B)
    (z : E × B) : B :=
  z.2 - c z.1 - V (N z.2)

theorem flowIntegralResidual_eq_zero_iff
    (c : E →L[ℝ] B) (V : B →L[ℝ] B) (N : B → B) (a : E) (γ : B) :
    flowIntegralResidual c V N (a, γ) = 0 ↔ γ = c a + V (N γ) := by
  constructor
  · intro h
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp h)).trans (add_comm _ _)
  · intro h
    apply sub_eq_zero.mpr
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

theorem flowIntegralResidual_contDiff
    (c : E →L[ℝ] B) (V : B →L[ℝ] B) (N : B → B)
    (hN : ContDiff ℝ ∞ N) : ContDiff ℝ ∞ (flowIntegralResidual c V N) := by
  exact (contDiff_snd.sub (c.contDiff.comp contDiff_fst)).sub
    (V.contDiff.comp (hN.comp contDiff_snd))

theorem flowIntegralResidual_hasFDerivAt
    (c : E →L[ℝ] B) (V : B →L[ℝ] B) (N : B → B)
    (a : E) (γ : B) (D : B →L[ℝ] B) (hD : HasFDerivAt N D γ) :
    HasFDerivAt (flowIntegralResidual c V N)
      (ContinuousLinearMap.snd ℝ E B - c ∘L ContinuousLinearMap.fst ℝ E B -
        V ∘L D ∘L ContinuousLinearMap.snd ℝ E B) (a, γ) := by
  exact ((hasFDerivAt_snd (𝕜 := ℝ) (p := (a, γ))).sub
    (c.hasFDerivAt.comp (a, γ) (hasFDerivAt_fst (p := (a, γ))))).sub
      (V.hasFDerivAt.comp (a, γ) (hD.comp (a, γ) (hasFDerivAt_snd (p := (a, γ)))))

/-- The partial derivative is the literal identity minus the linearized integral operator. -/
theorem flowIntegralResidual_partial
    (c : E →L[ℝ] B) (V : B →L[ℝ] B) (N : B → B)
    (a : E) (γ : B) (D : B →L[ℝ] B) (hD : HasFDerivAt N D γ) :
    fderiv ℝ (flowIntegralResidual c V N) (a, γ) ∘L
      ContinuousLinearMap.inr ℝ E B = 1 - V ∘L D := by
  rw [(flowIntegralResidual_hasFDerivAt c V N a γ D hD).fderiv]
  ext h
  simp

end Residual

section ConcretePath

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ}

/-- Smooth initial-label dependence of the unique solutions of the actual
whole-slab integral equation. Invertibility is discharged by the actual
Volterra operator, with no smallness condition on the slab length. -/
theorem flowPath_contDiff_of_integral_equation
    (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T × E, E))
    (A : C(Icc (0 : ℝ) T × E, E →L[ℝ] E))
    (K : ℝ≥0)
    (hu : ContDiff ℝ ∞ (flowPathSuperpositionTo u))
    (hder : ∀ γ : C(Icc (0 : ℝ) T, E),
      HasFDerivAt (flowPathSuperpositionTo u) (flowPathSuperpositionDerivative A γ) γ)
    (hA : ∀ (t : Icc (0 : ℝ) T) (x : E), ‖A (t, x)‖ ≤ K)
    (Γ : E → C(Icc (0 : ℝ) T, E))
    (hroot : ∀ a, Γ a = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT (flowPathSuperpositionTo u (Γ a)))
    (hunique : ∀ a γ, γ = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT (flowPathSuperpositionTo u γ) → γ = Γ a) :
    ContDiff ℝ ∞ Γ := by
  let c : E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
    ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)
  let Φ := flowIntegralResidual c (flowPathPrimitive hT) (flowPathSuperpositionTo u)
  apply contDiff_of_unique_implicit_branch Φ Γ
    (flowIntegralResidual_contDiff c (flowPathPrimitive hT) (flowPathSuperpositionTo u) hu)
  · intro a
    exact (flowIntegralResidual_eq_zero_iff c (flowPathPrimitive hT)
      (flowPathSuperpositionTo u) a (Γ a)).mpr (hroot a)
  · intro a γ hγ
    exact hunique a γ ((flowIntegralResidual_eq_zero_iff c (flowPathPrimitive hT)
      (flowPathSuperpositionTo u) a γ).mp hγ)
  · intro a
    rw [flowIntegralResidual_partial c (flowPathPrimitive hT)
      (flowPathSuperpositionTo u) a (Γ a) (flowPathSuperpositionDerivative A (Γ a)) (hder (Γ a))]
    exact one_sub_flowVolterra_isInvertible hT (flowPathSuperpositionTo A (Γ a)) K
      (fun t => hA t (Γ a t))

end ConcretePath

section PeriodicVelocity

open ClassicalMechanics NSEMaxwell.Classical

/-- The actual spatial derivative coefficient restricted to the compact time domain. -/
def flowVelocityDerivativeMap {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u) :
    C(Icc (0 : ℝ) T × Vec, Vec →L[ℝ] Vec) where
  toFun z := fderiv ℝ (u z.1) z.2
  continuous_toFun := (flow_spatial_fderiv_continuousOn hT hu).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun z => z.1.property)

/-- The path derivative formula has all spatial calculus assumptions discharged. -/
theorem periodic_velocity_superposition_hasFDerivAt {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (γ : C(Icc (0 : ℝ) T, Vec)) :
    HasFDerivAt (flowPathSuperpositionTo (flowVelocityMap hu))
      (flowPathSuperpositionDerivative (flowVelocityDerivativeMap hT hu) γ) γ := by
  obtain ⟨K, hK⟩ := flow_family_uniform_lipschitz hT
    (flow_family_fderiv_contDiffOn hT hu)
    (fun t ht => NSEMaxwell.PeriodicIntegration.fderiv_periodic (hp t ht))
  apply flowPathSuperposition_hasFDerivAt_of_lipschitz_derivative
    (flowVelocityMap hu) (flowVelocityDerivativeMap hT hu) K
  · intro t x
    exact ((finite_velocity_slice_smooth hu t.property).differentiable (by simp) x).hasFDerivAt
  · intro t
    exact hK t t.property

/-- Smooth dependence for actual periodic-velocity integral curves, conditional
only on their literal integral equation and its uniqueness. -/
theorem periodic_velocity_path_contDiff_of_integral_equation {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (Γ : Vec → C(Icc (0 : ℝ) T, Vec))
    (hroot : ∀ a, Γ a = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT.le (flowPathSuperpositionTo (flowVelocityMap hu) (Γ a)))
    (hunique : ∀ a γ, γ = ContinuousMap.const (Icc (0 : ℝ) T) a +
      flowPathPrimitive hT.le (flowPathSuperpositionTo (flowVelocityMap hu) γ) → γ = Γ a) :
    ContDiff ℝ ∞ Γ := by
  obtain ⟨K, hK⟩ := flow_periodic_uniform_bound
    (flow_spatial_fderiv_continuousOn hT hu)
    (fun t ht => NSEMaxwell.PeriodicIntegration.fderiv_periodic (hp t ht))
  exact flowPath_contDiff_of_integral_equation hT.le (flowVelocityMap hu)
    (flowVelocityDerivativeMap hT hu) K
    (periodic_velocity_superposition_contDiff hT hu hp)
    (periodic_velocity_superposition_hasFDerivAt hT hu hp)
    (fun t x => hK t t.property x) Γ hroot hunique

/-- E09 for the actual selected ODE paths: existence and integral uniqueness
are native consequences of the bounded periodic velocity hypotheses. -/
theorem selectedFlowPath_contDiff {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    {B K : ℝ≥0} (h : Flow.SlabODEData T u B K) :
    ContDiff ℝ ∞ (selectedFlowPath h hT.le) := by
  have heq : flowVelocityMap hu = flowSlabVelocity h := by
    ext z
    rfl
  apply periodic_velocity_path_contDiff_of_integral_equation hT hu hp
    (selectedFlowPath h hT.le)
  · intro a
    rw [heq]
    exact selectedFlowPath_integral_equation h hT.le a
  · intro a γ hγ
    rw [heq] at hγ
    exact selectedFlowPath_integral_unique h hT.le a γ hγ

/-- The selected C-infinity Banach path family exists under exactly the smooth
periodic velocity premises; no flow realization or smoothness is admitted. -/
theorem periodic_velocity_exists_smooth_flow_path {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    ∃ B K : ℝ≥0, ∃ h : Flow.SlabODEData T u B K,
      ContDiff ℝ ∞ (selectedFlowPath h hT.le) := by
  obtain ⟨B, K, h⟩ := Flow.smooth_periodic_slabODEData hT hu hp
  exact ⟨B, K, h, selectedFlowPath_contDiff hT hu hp h⟩

end PeriodicVelocity

end

end ClassicalMechanicsAssembly
