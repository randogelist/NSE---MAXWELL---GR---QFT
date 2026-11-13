import ClassicalMechanics.Material

/-!
# Smooth periodic material fields and literal decoding

The pressure is the actual pullback `p(t, eta(t,a))`; its smoothness and
periodicity follow from the material path.  The actual flow ODE supplies the
initial material velocity and identifies decoded fields with their original
Eulerian fields on the closed slab.  No pressure normalization is imposed.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped ContDiff

noncomputable section

/-- Smooth pressure remains jointly smooth under the actual material pullback. -/
theorem material_pressure_pullback_smooth {T : ℝ} {η ρ : Velocity} {p : Pressure}
    (hη : MaterialPathOn T η ρ) (hp : SmoothPressureOn T p) :
    SmoothPressureOn T (fun t a => p t (η t a)) := by
  have hmap : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => (z.1, η z.1 z.2))
      (finiteSpacetime T) := contDiffOn_fst.prodMk hη.smooth
  exact hp.comp hmap (fun _ hz => hz)

/-- Unit-lattice equivariance transports the original periodic pressure gauge. -/
theorem material_pressure_pullback_periodic {T : ℝ} {η ρ : Velocity} {p : Pressure}
    (hη : MaterialPathOn T η ρ)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (p t)) :
    ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (fun a => p t (η t a)) := by
  intro t ht a i
  change p t (η t (a + unitVector i)) = p t (η t a)
  rw [hη.lattice_equivariant t ht a i]
  exact hp t ht (η t a) i

/-- The supplied flow ODE realizes the prescribed initial velocity. -/
theorem material_initial_velocity_of_flow {T : ℝ} (hT : 0 ≤ T)
    {u η ρ : Velocity} {a : Field}
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : Vec,
      materialVelocity T η t b = u t (η t b))
    (hinitial : u 0 = a) :
    materialVelocity T η 0 = a := by
  funext b
  rw [hflow 0 ⟨le_rfl, hT⟩ b, hη.initial_configuration, hinitial]

/-- Decoding the material velocity recovers the original velocity on the slab. -/
theorem material_velocity_decode_of_flow {T : ℝ} {u η ρ : Velocity}
    (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      eulerianVelocityOfMaterial T η ρ t = u t := by
  intro t ht
  funext x
  change materialVelocity T η t (ρ t x) = u t x
  rw [hflow t ht (ρ t x), hη.right_inverse t ht x]

/-- Decoding the literal pressure pullback recovers the original pressure gauge. -/
theorem material_pressure_decode_of_pullback {T : ℝ} {η ρ : Velocity}
    (hη : MaterialPathOn T η ρ) (p : Pressure) :
    ∀ t ∈ Icc (0 : ℝ) T,
      eulerianPressureOfMaterial ρ (fun s a => p s (η s a)) t = p t := by
  intro t ht
  funext x
  change p t (η t (ρ t x)) = p t x
  rw [hη.right_inverse t ht x]

/-- The actual material velocity is jointly smooth once the flow ODE is supplied. -/
theorem material_velocity_smooth_of_flow {T : ℝ} {u η ρ : Velocity}
    (hη : MaterialPathOn T η ρ) (hu : SmoothVelocityOn T u)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    SmoothVelocityOn T (materialVelocity T η) := by
  have hmap : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => (z.1, η z.1 z.2))
      (finiteSpacetime T) := contDiffOn_fst.prodMk hη.smooth
  have hcomp := hu.comp hmap (fun _ hz => hz)
  apply hcomp.congr
  intro z hz
  exact hflow z.1 hz z.2

/-- The actual material velocity inherits spatial periodicity from the flow ODE. -/
theorem material_velocity_periodic_of_flow {T : ℝ} {u η ρ : Velocity}
    (hη : MaterialPathOn T η ρ)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (materialVelocity T η t) := by
  intro t ht a i
  rw [hflow t ht (a + unitVector i), hflow t ht a,
    hη.lattice_equivariant t ht a i]
  exact hu t ht (η t a) i

end

end ClassicalMechanicsAssembly
