import ClassicalMechanicsAssembly.LiteratureInputs

/-!
# Material equation closure with named literature axioms

The first theorem uses the L1 flow axiom and the native L2 diffusion theorem.
Its historical name is retained for compatibility. The second has the same
conclusion and invokes the native supplied-flow equation theorem directly.
Both routes now have L1 as their only nonfoundational axiom. Both construct a path for a supplied smooth velocity
field and establish equation equivalence with the literal pressure pullback.
Neither theorem asserts NSE existence from initial data or a full solution-set
bijection with pressure-normalization, energy, or variational transport.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Literature

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- Compatibility root: L1 is assumed and L2 is proved natively. -/
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

/-- The same closure with only the L1 analytic axiom. -/
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
