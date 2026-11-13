import ClassicalMechanicsAssembly.LiteratureInputs

/-!
# Material equation closure with named literature axioms

The first theorem explicitly uses both authorized inputs. The second has the
same conclusion and uses only `L1`, because the native Piola assembly already
proves the `L2` contract. Both construct a path for a supplied smooth velocity
field and establish equation equivalence with the literal pressure pullback.
Neither theorem asserts NSE existence from initial data or a full solution-set
bijection with pressure-normalization, energy, or variational transport.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Literature

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- Conditional material equation closure with explicit dependence on L1 and L2. -/
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

/-- The same closure after eliminating L2 by the existing native diffusion proof. -/
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
