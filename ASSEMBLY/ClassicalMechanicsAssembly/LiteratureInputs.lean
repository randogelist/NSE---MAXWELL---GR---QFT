import ClassicalMechanicsAssembly.FlowRealization

/-!
# Native compatibility contracts

`L1` retains the exact former FLOW axiom signature and invokes the native
finite-slab flow-realization theorem. `L2` and `L2_native` retain their native
diffusion proofs. No custom axiom is declared in this compatibility module.
Fresh matching external audits are required for the changed declarations.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Literature

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- O_FLOW: smooth periodic solenoidal fields admit a normalized material path. -/
theorem L1 {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u)
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∃ η ρ : Velocity,
      MaterialPathOn T η ρ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
        materialVelocity T η t a = u t (η t a) :=
  ClassicalMechanicsAssembly.L1_native hT hu hperiodic hdiv

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
