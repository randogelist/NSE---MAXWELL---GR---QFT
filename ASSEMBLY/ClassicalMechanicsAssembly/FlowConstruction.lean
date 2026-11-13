import ClassicalMechanicsAssembly.FlowTrajectories
import ClassicalMechanicsAssembly.FlowInverse
import ClassicalMechanicsAssembly.FlowVariational
import ClassicalMechanicsAssembly.Equation

/-!
The native construction reduces the exact L1 contract to one analytic edge:
joint smooth dependence of the actual ODE family on time and initial label.
That edge is an explicit theorem argument, not an axiom or a claimed proof.
Inverse smoothness and determinant one are derived here from the forward edge.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical Flow
open scoped ContDiff NNReal

noncomputable section

/-- Joint continuity of the actual backward family from native stability estimates. -/
theorem constructed_inverse_continuousOn {T : ℝ} {u : Velocity} {B K : ℝ≥0}
    (h : SlabODEData T u B K) (hT : 0 ≤ T) :
    ContinuousOn (fun z : ℝ × Vec => inverseFlow h z.1 z.2) (finiteSpacetime T) := by
  apply continuousOn_inverse_flow_of_estimate (B := B)
    (C := Real.toNNReal (Real.exp ((K : ℝ) * T)))
  intro t ht s hs x y
  apply inverse_flow_dist_le (inverseFlow_flow h hT) (flow_inverseFlow h hT)
    (inverseFlow_lipschitz h hT) _ ht hs x y
  intro q hq r hr a
  exact (trajectory_time_lipschitz h ⟨0, ⟨le_rfl, hT⟩⟩ a).dist_le_mul q hq r hr

/-- All remaining path fields follow from smoothness of the constructed forward flow. -/
theorem constructed_materialPathOn {T : ℝ} (hT : 0 < T)
    {u : Velocity} {B K : ℝ≥0} (h : SlabODEData T u B K)
    (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    (hforward : SmoothVelocityOn T (flow h hT.le)) :
    MaterialPathOn T (flow h hT.le) (inverseFlow h) := by
  have hi : flow h hT.le 0 = fun a : Vec => a := funext (flow_initial h hT.le)
  have hf := flow_materialVelocity h hT
  have hdet := FLOW_JACOBIAN_ONE hT hu hforward hi hf hdiv
  exact materialPathOn_of_smooth_inverse_data hT hforward
    (constructed_inverse_continuousOn h hT.le)
    (inverseFlow_flow h hT.le) (flow_inverseFlow h hT.le)
    (flow_lattice_equivariant h hT.le hp) hi hdet

/-- The precise unresolved smooth-dependence edge, with actual ODE hypotheses. -/
def JointFlowRegularity (T : ℝ) (u : Velocity) : Prop :=
  ∀ η : Velocity, η 0 = (fun a => a) →
    (∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      HasDerivWithinAt (fun s => η s a) (u t (η t a)) (Icc (0 : ℝ) T) t) →
    SmoothVelocityOn T η

/-- Exact L1 conclusion, conditional only on the named joint forward regularity edge. -/
theorem FLOW_REALIZATION_OF_JOINT_REGULARITY {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    (hregularity : JointFlowRegularity T u) :
    ∃ η ρ : Velocity, MaterialPathOn T η ρ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, materialVelocity T η t a = u t (η t a) := by
  obtain ⟨B, K, h⟩ := smooth_periodic_slabODEData hT hu hp
  have hs : SmoothVelocityOn T (flow h hT.le) :=
    hregularity _ (funext (flow_initial h hT.le))
      (fun t ht a => flow_hasDerivWithinAt h hT.le a t ht)
  exact ⟨flow h hT.le, inverseFlow h,
    constructed_materialPathOn hT h hu hp hdiv hs, flow_materialVelocity h hT⟩

/-- Equation closure through the newly constructed path; no literature axiom is imported. -/
theorem MATERIAL_EQUATION_OF_JOINT_REGULARITY {ν T : ℝ} (hT : 0 < T)
    {u : Velocity} {p : Pressure} (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    (hregularity : JointFlowRegularity T u) :
    ∃ η ρ : Velocity, MaterialPathOn T η ρ ∧
      ((∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
        finiteMaterialAcceleration T u t x + gradient (p t) x = ν • laplacian (u t) x) ↔
        MaterialEquationOn ν T η (fun t a => p t (η t a))) := by
  obtain ⟨η, ρ, hη, hflow⟩ := FLOW_REALIZATION_OF_JOINT_REGULARITY hT hu hperiodic hdiv hregularity
  exact ⟨η, ρ, hη, CLASSICAL_MECHANICS_MATERIAL_OF_FLOW hT hu hp hη hflow⟩

end

end ClassicalMechanicsAssembly
