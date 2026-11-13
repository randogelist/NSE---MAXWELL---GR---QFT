import ClassicalMechanicsAssembly.FlowJoint
import ClassicalMechanicsAssembly.FlowConstruction

/-!
# Native finite-slab flow realization

The exact L1 statement is assembled from actual periodic ODE trajectories,
Banach path-space smooth dependence, differentiated integral equations,
the variational ODE, and smooth inversion on the closed spacetime slab.
No literature-input module is imported. Promotion requires matching external
compiler and theorem-level axiom-audit evidence for these exact declarations.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical Flow
open scoped ContDiff NNReal

noncomputable section

/-- Joint regularity of every actual flow family with identity initial data. -/
theorem jointFlowRegularity_of_smooth_periodic {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    JointFlowRegularity T u := by
  obtain ⟨B, K, h⟩ := smooth_periodic_slabODEData hT hu hp
  intro η hη0 hη
  have hs := constructed_flow_smooth hT hu hp h
  apply hs.congr
  intro z hz
  have he := solution_unique h ⟨0, ⟨le_rfl, hT.le⟩⟩
    (f := fun t => η t z.2) (g := fun t => flow h hT.le t z.2)
    (fun t ht => hη t ht z.2)
    (fun t ht => flow_hasDerivWithinAt h hT.le z.2 t ht)
    (by rw [hη0, flow_initial])
  exact he hz

/-- Exact native replacement candidate for the sole remaining L1 literature input. -/
theorem L1_native {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0) :
    ∃ η ρ : Velocity, MaterialPathOn T η ρ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialVelocity T η t a = u t (η t a) := by
  obtain ⟨B, K, h⟩ := smooth_periodic_slabODEData hT hu hperiodic
  have hs := constructed_flow_smooth hT hu hperiodic h
  exact ⟨flow h hT.le, inverseFlow h,
    constructed_materialPathOn hT h hu hperiodic hdiv hs,
    flow_materialVelocity h hT⟩

/-- Native flow realization feeds the previously derived exact material equation equivalence. -/
theorem CLASSICAL_MECHANICS_MATERIAL_NATIVE {ν T : ℝ} (hT : 0 < T)
    {u : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0) :
    ∃ η ρ : Velocity, MaterialPathOn T η ρ ∧
      ((∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
        finiteMaterialAcceleration T u t x + gradient (p t) x = ν • laplacian (u t) x) ↔
        MaterialEquationOn ν T η (fun t a => p t (η t a))) := by
  obtain ⟨η, ρ, hη, hflow⟩ := L1_native hT hu hperiodic hdiv
  exact ⟨η, ρ, hη, CLASSICAL_MECHANICS_MATERIAL_OF_FLOW hT hu hp hη hflow⟩

end

end ClassicalMechanicsAssembly
