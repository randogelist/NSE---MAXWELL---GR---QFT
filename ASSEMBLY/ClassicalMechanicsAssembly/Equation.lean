import ClassicalMechanicsAssembly.NativeEndpoints
import ClassicalMechanicsAssembly.PiolaTransport

/-!
Deterministic equation transport from the supplied smooth material path and
its actual flow equation. The transformed diffusion is derived in
`PiolaTransport`; pressure is the literal scalar pullback. Existence of the
path from a periodic Eulerian velocity is a separate obligation.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- All five pullback identities from smoothness, the supplied path, and its ODE. -/
theorem material_pullback_of_flow {T : ℝ} (hT : 0 < T)
    {u η ρ : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    MaterialPullbackIdentities T u p η (fun t a => p t (η t a)) :=
  material_pullback_of_flow_and_diffusion hT hu hp hη hflow
    (fun _ _ _ => rfl)
    (CLASSICAL_MECHANICS_DIFFUSION_REALIZATION hu hη hflow)

theorem eulerian_equation_implies_material_of_flow
    {ν T : ℝ} (hT : 0 < T) {u η ρ : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hE : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x) :
    MaterialEquationOn ν T η (fun t a => p t (η t a)) :=
  eulerian_equation_to_material (material_pullback_of_flow hT hu hp hη hflow) hE

theorem material_equation_implies_eulerian_of_flow
    {ν T : ℝ} (hT : 0 < T) {u η ρ : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hM : MaterialEquationOn ν T η (fun t a => p t (η t a))) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x :=
  material_equation_to_eulerian (material_pullback_of_flow hT hu hp hη hflow)
    (fun _ ht => material_path_surjective hη ht) hM

/-- Supplied-flow equation equivalence; no diffusion admission remains. -/
theorem CLASSICAL_MECHANICS_MATERIAL_OF_FLOW
    {ν T : ℝ} (hT : 0 < T) {u η ρ : Velocity} {p : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x) ↔
      MaterialEquationOn ν T η (fun t a => p t (η t a)) :=
  ⟨eulerian_equation_implies_material_of_flow hT hu hp hη hflow,
    material_equation_implies_eulerian_of_flow hT hu hp hη hflow⟩

end

end ClassicalMechanicsAssembly
