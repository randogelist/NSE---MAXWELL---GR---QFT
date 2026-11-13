import ClassicalMechanics.MaterialGradient
import ClassicalMechanics.Piola

/-! Deterministic material equation assembly with the remaining premises explicit. -/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical Set

noncomputable section

theorem material_inverse_transpose_divergence_zero {T : ℝ} {η ρ : Velocity}
    (hη : MaterialPathOn T η ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    tensorDivergence (fun a => (inverseDeformationGradient η t a).transpose) = 0 := by
  apply tensorDivergence_inverse_transpose_of_det_one
    (finite_velocity_slice_smooth hη.smooth ht)
  exact hη.determinant_one t ht

/-- The acceleration and pressure-gradient premises are native theorems here.
The construction of the path and the transformed diffusion identity remain explicit. -/
theorem material_pullback_of_flow_and_diffusion {T : ℝ} (hT : 0 < T)
    {u η ρ : Velocity} {p π : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hπ : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, π t a = p t (η t a))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a = NSEMaxwell.Classical.laplacian (u t) (η t a)) :
    MaterialPullbackIdentities T u p η π :=
  materialPullbackIdentities_of_flow hT hu hη.smooth hflow hπ
    (material_pressure_gradient_pullback_on hη hp hπ) hdiff

/-- Exact conditional equation equivalence; no full solution-set bijection is asserted. -/
theorem CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION
    {ν T : ℝ} (hT : 0 < T) {u η ρ : Velocity} {p π : Pressure}
    (hu : SmoothVelocityOn T u) (hp : SmoothPressureOn T p)
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hπ : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, π t a = p t (η t a))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a = NSEMaxwell.Classical.laplacian (u t) (η t a)) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x) ↔ MaterialEquationOn ν T η π :=
  eulerian_equation_iff_material
    (material_pullback_of_flow_and_diffusion hT hu hp hη hflow hπ hdiff) hη

end

end ClassicalMechanics
