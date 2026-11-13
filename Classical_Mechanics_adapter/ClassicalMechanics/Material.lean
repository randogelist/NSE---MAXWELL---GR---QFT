import ClassicalMechanics.TimeCalculus

/-!
# Native material-coordinate endpoint and conditional equation transport

The deformation gradient, its matrix inverse, the material acceleration and
the transformed viscosity are actual differential expressions.  The path
predicate includes a jointly smooth inverse, unit-lattice equivariance, the
identity initial configuration, and determinant one.

`MaterialPullbackIdentities` lists the analytic edges still required for a
flow/Piola realization.  It is a theorem argument, never an axiom or an
inhabited instance.  The equation transport theorems below discharge only the
algebraic implication from these explicitly supplied identities.
-/

set_option autoImplicit false

open Set
open scoped BigOperators ContDiff

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

/-- Rows are vector components and columns are differentiation directions. -/
def materialGradientMatrix (v : Field) : StressField :=
  fun a i j => coordinateDerivative v j a i

def deformationGradient (η : Velocity) (t : ℝ) : StressField :=
  materialGradientMatrix (η t)

def inverseDeformationGradient (η : Velocity) (t : ℝ) : StressField :=
  fun a => (deformationGradient η t a)⁻¹

def materialVelocity (T : ℝ) (η : Velocity) : Velocity :=
  fun t a => finiteTimeDerivative T η t a

def materialPathAcceleration (T : ℝ) (η : Velocity) (t : ℝ) (a : Vec) : Vec :=
  finiteTimeDerivative T (materialVelocity T η) t a

/-- The actual `Aᵀ ∇ₐ π` expression, represented in Euclidean coordinates. -/
def materialPressureGradient (η : Velocity) (π : Pressure)
    (t : ℝ) (a : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    ∑ j : Fin 3, inverseDeformationGradient η t a j i *
      NSEMaxwell.Classical.gradient (π t) a j)

/-- The order is precisely `Dₐ V * A * Aᵀ`. -/
def materialViscousTensor (T : ℝ) (η : Velocity) (t : ℝ) : StressField :=
  fun a => materialGradientMatrix (materialVelocity T η t) a *
    inverseDeformationGradient η t a *
      (inverseDeformationGradient η t a).transpose

def materialDiffusion (T : ℝ) (η : Velocity) (t : ℝ) : Field :=
  tensorDivergence (materialViscousTensor T η t)

/-- Smooth identity-normalized volume-preserving torus path, encoded by lifts. -/
structure MaterialPathOn (T : ℝ) (η ρ : Velocity) : Prop where
  smooth : SmoothVelocityOn T η
  inverse_smooth : SmoothVelocityOn T ρ
  left_inverse : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ρ t (η t a) = a
  right_inverse : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, η t (ρ t x) = x
  lattice_equivariant : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ∀ i : Fin 3,
    η t (a + unitVector i) = η t a + unitVector i
  initial_configuration : η 0 = fun a => a
  determinant_one : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    (deformationGradient η t a).det = 1

theorem material_path_surjective {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Function.Surjective (η t) := by
  intro x
  exact ⟨ρ t x, h.right_inverse t ht x⟩

theorem material_inverse_initial {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) (hT : 0 ≤ T) :
    ρ 0 = fun a => a := by
  funext a
  have hi := h.left_inverse 0 ⟨le_rfl, hT⟩ a
  simpa only [h.initial_configuration] using hi

theorem material_displacement_periodic {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    SpatialPeriodic (fun a => η t a - a) := by
  intro a i
  rw [h.lattice_equivariant t ht a i]
  abel

theorem material_inverse_lattice_equivariant {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (x : Vec) (i : Fin 3) :
    ρ t (x + unitVector i) = ρ t x + unitVector i := by
  have hi := h.left_inverse t ht (ρ t x + unitVector i)
  rw [h.lattice_equivariant t ht (ρ t x) i, h.right_inverse t ht x] at hi
  exact hi

theorem deformation_det_ne_zero {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    (deformationGradient η t a).det ≠ 0 := by
  rw [h.determinant_one t ht a]
  exact one_ne_zero

/-- M1 with the pressure gradient moved to the left-hand side. -/
def MaterialEquationOn (ν T : ℝ) (η : Velocity) (π : Pressure) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    materialPathAcceleration T η t a + materialPressureGradient η π t a =
      ν • materialDiffusion T η t a

theorem material_equation_force_form (ν T : ℝ) (η : Velocity) (π : Pressure) :
    MaterialEquationOn ν T η π ↔
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialPathAcceleration T η t a =
          -materialPressureGradient η π t a + ν • materialDiffusion T η t a := by
  constructor
  · intro h t ht a
    calc
      materialPathAcceleration T η t a =
          (materialPathAcceleration T η t a + materialPressureGradient η π t a) -
            materialPressureGradient η π t a := by abel
      _ = ν • materialDiffusion T η t a - materialPressureGradient η π t a := by
        rw [h t ht a]
      _ = -materialPressureGradient η π t a + ν • materialDiffusion T η t a := by abel
  · intro h t ht a
    rw [h t ht a]
    abel

/-- Native finite-slab material solution, including the pressure gauge. -/
structure MaterialSolutionOn (ν : ℝ) (a : Field) (T : ℝ)
    (η ρ : Velocity) (π : Pressure) : Prop where
  path : MaterialPathOn T η ρ
  pressure_smooth : SmoothPressureOn T π
  pressure_periodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (π t)
  pressure_normalized : ∀ t ∈ Icc (0 : ℝ) T, scalarMean (π t) = 0
  initial_velocity : materialVelocity T η 0 = a
  equation : MaterialEquationOn ν T η π

def eulerianVelocityOfMaterial (T : ℝ) (η ρ : Velocity) : Velocity :=
  fun t x => materialVelocity T η t (ρ t x)

def eulerianPressureOfMaterial (ρ : Velocity) (π : Pressure) : Pressure :=
  fun t x => π t (ρ t x)

theorem material_velocity_decode_pullback {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    eulerianVelocityOfMaterial T η ρ t (η t a) = materialVelocity T η t a := by
  unfold eulerianVelocityOfMaterial
  rw [h.left_inverse t ht a]

theorem material_pressure_decode_pullback {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) (π : Pressure)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    eulerianPressureOfMaterial ρ π t (η t a) = π t a := by
  unfold eulerianPressureOfMaterial
  rw [h.left_inverse t ht a]

theorem material_decoded_pressure_periodic {T : ℝ} {η ρ : Velocity}
    (h : MaterialPathOn T η ρ) {π : Pressure}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hπ : SpatialPeriodic (π t)) :
    SpatialPeriodic (eulerianPressureOfMaterial ρ π t) := by
  intro x i
  unfold eulerianPressureOfMaterial
  rw [material_inverse_lattice_equivariant h ht x i]
  exact hπ (ρ t x) i

theorem material_decoded_initial {T : ℝ} {η ρ : Velocity} {a : Field}
    (h : MaterialPathOn T η ρ) (hT : 0 ≤ T)
    (hV : materialVelocity T η 0 = a) :
    eulerianVelocityOfMaterial T η ρ 0 = a := by
  funext x
  change materialVelocity T η 0 (ρ 0 x) = a x
  rw [material_inverse_initial h hT, hV]

/--
Explicit analytic premises corresponding to flow acceleration, gradient
pullback, and incompressible Piola diffusion.  Their construction from smooth
Eulerian fields and a normalized flow remains a separate proof obligation.
-/
structure MaterialPullbackIdentities (T : ℝ) (u : Velocity) (p : Pressure)
    (η : Velocity) (π : Pressure) : Prop where
  velocity : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    materialVelocity T η t a = u t (η t a)
  pressure : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    π t a = p t (η t a)
  acceleration : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    materialPathAcceleration T η t a = finiteMaterialAcceleration T u t (η t a)
  pressure_gradient : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    materialPressureGradient η π t a =
      NSEMaxwell.Classical.gradient (p t) (η t a)
  diffusion : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
    materialDiffusion T η t a = NSEMaxwell.Classical.laplacian (u t) (η t a)

/-- Acceleration is derived from the native closed-slab chain rule. -/
theorem materialPullbackIdentities_of_flow {T : ℝ} (hT : 0 < T)
    {u η : Velocity} {p π : Pressure}
    (hu : SmoothVelocityOn T u) (hη : SmoothVelocityOn T η)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hp : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, π t a = p t (η t a))
    (hgrad : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialPressureGradient η π t a =
        NSEMaxwell.Classical.gradient (p t) (η t a))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a = NSEMaxwell.Classical.laplacian (u t) (η t a)) :
    MaterialPullbackIdentities T u p η π := by
  refine ⟨hflow, hp, ?_, hgrad, hdiff⟩
  intro t ht a
  exact finite_flow_acceleration hT hu hη hflow ht a

def eulerianResidualOn (ν T : ℝ) (u : Velocity) (p : Pressure)
    (t : ℝ) (x : Vec) : Vec :=
  finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x -
    ν • NSEMaxwell.Classical.laplacian (u t) x

def materialResidualOn (ν T : ℝ) (η : Velocity) (π : Pressure)
    (t : ℝ) (a : Vec) : Vec :=
  materialPathAcceleration T η t a + materialPressureGradient η π t a -
    ν • materialDiffusion T η t a

theorem material_residual_pullback {T : ℝ} {u η : Velocity} {p π : Pressure}
    (h : MaterialPullbackIdentities T u p η π) (ν : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    materialResidualOn ν T η π t a = eulerianResidualOn ν T u p t (η t a) := by
  unfold materialResidualOn eulerianResidualOn
  rw [h.acceleration t ht a, h.pressure_gradient t ht a, h.diffusion t ht a]

theorem eulerian_equation_to_material {ν T : ℝ} {u η : Velocity} {p π : Pressure}
    (h : MaterialPullbackIdentities T u p η π)
    (hE : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x) :
    MaterialEquationOn ν T η π := by
  intro t ht a
  rw [h.acceleration t ht a, h.pressure_gradient t ht a, h.diffusion t ht a]
  exact hE t ht (η t a)

theorem material_equation_to_eulerian {ν T : ℝ} {u η : Velocity} {p π : Pressure}
    (h : MaterialPullbackIdentities T u p η π)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, Function.Surjective (η t))
    (hM : MaterialEquationOn ν T η π) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x := by
  intro t ht x
  obtain ⟨a, rfl⟩ := hη t ht x
  rw [← h.acceleration t ht a, ← h.pressure_gradient t ht a, ← h.diffusion t ht a]
  exact hM t ht a

theorem eulerian_equation_iff_material {ν T : ℝ} {u η ρ : Velocity}
    {p π : Pressure} (h : MaterialPullbackIdentities T u p η π)
    (hη : MaterialPathOn T η ρ) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x + NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x) ↔
      MaterialEquationOn ν T η π := by
  constructor
  · exact eulerian_equation_to_material h
  · exact material_equation_to_eulerian h (fun _ ht => material_path_surjective hη ht)

/-- The prepared native NSE solution supplies the Eulerian differential equation. -/
theorem ns_solution_material_equation {ν T : ℝ} {a : Field}
    {u η : Velocity} {p π : Pressure} (hu : NSSolutionOn ν a T u p)
    (h : MaterialPullbackIdentities T u p η π) :
    MaterialEquationOn ν T η π := by
  apply eulerian_equation_to_material h
  intro t ht x
  exact hu.equation t ht x

end

end ClassicalMechanics
