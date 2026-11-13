import ClassicalMechanicsAssembly.Equation

/-!
# Explicit literature inputs

The user-authorized axioms `L1` and `L2` have exactly the FLOW and DIFFUSION
contracts in Section 1 of `CLASSICAL_MECHANICS_FLOW_PIOLA_INPUTS_B_TIER.txt`.
They are isolated from the existing standard-only assembly entry point.

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

/-- O_DIFF: the exact spatial diffusion pullback; no positivity of T is added. -/
axiom L2 {T : ℝ} {u η ρ : Velocity}
    (hu : SmoothVelocityOn T u) (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialDiffusion T η t a =
        NSEMaxwell.Classical.laplacian (u t) (η t a)

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
