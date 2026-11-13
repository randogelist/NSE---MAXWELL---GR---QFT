import ClassicalMechanicsAssembly.Equation

/-!
# Explicit literature inputs

`L1` is the remaining user-authorized FLOW axiom. `L2` is a theorem with
the exact DIFFUSION contract from Section 1 of
`CLASSICAL_MECHANICS_FLOW_PIOLA_INPUTS_B_TIER.txt`, proved by native Piola
transport. These contracts remain isolated from the standard-only entry point.

`L2_native` has the same type as `L2` and uses the existing native diffusion
theorem. Thus `L2` can be eliminated from the material equation closure;
the flow-existence assumption `L1` remains explicitly visible.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Literature

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- O_FLOW: smooth periodic solenoidal fields admit a normalized material path. -/
axiom L1 {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∃ η ρ : Velocity,
      MaterialPathOn T η ρ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialVelocity T η t a = u t (η t a)

/-- O_DIFF is a native theorem; no positivity of T or literature axiom is added. -/
theorem L2 {T : ℝ} {u η ρ : Velocity}
    (hu : SmoothVelocityOn T u) (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a =
        NSEMaxwell.Classical.laplacian (u t) (η t a) :=
  ClassicalMechanicsAssembly.CLASSICAL_MECHANICS_DIFFUSION_REALIZATION hu hη hflow

/-- The literal L2 contract is already realized by the native Piola assembly. -/
theorem L2_native {T : ℝ} {u η ρ : Velocity}
    (hu : SmoothVelocityOn T u) (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a =
        NSEMaxwell.Classical.laplacian (u t) (η t a) :=
  ClassicalMechanicsAssembly.CLASSICAL_MECHANICS_DIFFUSION_REALIZATION hu hη hflow

end

end ClassicalMechanicsAssembly.Literature
