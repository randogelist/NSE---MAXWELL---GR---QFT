import ClassicalMechanicsAssembly.LiteratureInputs

/-!
# Native material equation compatibility routes

Both historical theorem names are retained. L1 and L2 are native theorems;
their exact original signatures and the two root conclusions are unchanged.
The roots construct a path for a supplied smooth periodic divergence-free
velocity and establish equation equivalence with literal pressure pullback.
No arbitrary-data NSE existence or full solution-set bijection is asserted.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Literature

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- Compatibility root using the native L1 and L2 theorems. -/
theorem CLASSICAL_MECHANICS_MATERIAL_FROM_L1_L2
    {ν T : ℝ} (hT : 0 < T) {u : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∃ η ρ : Velocity,
      MaterialPathOn T η ρ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialVelocity T η t a = u t (η t a)) ∧
      ((∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
        finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
          ν • NSEMaxwell.Classical.laplacian (u t) x) ↔
        MaterialEquationOn ν T η (fun t a => p t (η t a))) := by
  obtain ⟨η, ρ, hη, hflow⟩ := L1 hT hu hperiodic hdiv
  refine ⟨η, ρ, hη, hflow, ?_⟩
  exact ClassicalMechanics.CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION
    hT hu hp hη hflow (fun _ _ _ => rfl) (L2 hu hη hflow)

/-- The same closure using native flow realization and the native equation bridge. -/
theorem CLASSICAL_MECHANICS_MATERIAL_FROM_L1
    {ν T : ℝ} (hT : 0 < T) {u : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∃ η ρ : Velocity,
      MaterialPathOn T η ρ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialVelocity T η t a = u t (η t a)) ∧
      ((∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
        finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
          ν • NSEMaxwell.Classical.laplacian (u t) x) ↔
        MaterialEquationOn ν T η (fun t a => p t (η t a))) := by
  obtain ⟨η, ρ, hη, hflow⟩ := L1 hT hu hperiodic hdiv
  refine ⟨η, ρ, hη, hflow, ?_⟩
  exact ClassicalMechanicsAssembly.CLASSICAL_MECHANICS_MATERIAL_OF_FLOW
    hT hu hp hη hflow

end

end ClassicalMechanicsAssembly.Literature
