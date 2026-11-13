import ClassicalMechanics.Definitions

/-!
# Finite normalized-pressure solution predicates

Both concrete formulations use the same actual `derivWithin` on `Icc 0 T`,
joint `ContDiffOn` on the closed slab, and zero spatial pressure mean.
These are separate from the repository's global arbitrary-gauge predicates.
No restriction/normalization theorem between the two scopes is asserted here.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

def finiteSpacetime (T : ℝ) : Set (ℝ × Vec) :=
  {z | z.1 ∈ Icc (0 : ℝ) T}

def SmoothVelocityOn (T : ℝ) (u : Velocity) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (finiteSpacetime T)

def SmoothPressureOn (T : ℝ) (p : Pressure) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (finiteSpacetime T)

def finiteTimeDerivative (T : ℝ) (u : Velocity) (t : ℝ) (x : Vec) : Vec :=
  derivWithin (fun s : ℝ => u s x) (Icc (0 : ℝ) T) t

def finiteMaterialAcceleration (T : ℝ) (u : Velocity) (t : ℝ) (x : Vec) : Vec :=
  finiteTimeDerivative T u t x + convection (u t) x

theorem finite_velocity_slice_smooth {T : ℝ} {u : Velocity}
    (hu : SmoothVelocityOn T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (u t) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (finiteSpacetime T) at hu
  have hslice : ContDiff ℝ ∞ (fun x : Vec => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hmem : ∀ x : Vec, (t, x) ∈ finiteSpacetime T := fun _ => ht
  simpa only [Function.comp_def] using hu.comp_contDiff hslice hmem

theorem finite_pressure_slice_smooth {T : ℝ} {p : Pressure}
    (hp : SmoothPressureOn T p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (p t) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (finiteSpacetime T) at hp
  have hslice : ContDiff ℝ ∞ (fun x : Vec => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hmem : ∀ x : Vec, (t, x) ∈ finiteSpacetime T := fun _ => ht
  simpa only [Function.comp_def] using hp.comp_contDiff hslice hmem

/-- The exact smooth finite-slab NSE predicate, including pressure normalization. -/
structure NSSolutionOn (ν : ℝ) (a : Field) (T : ℝ)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : SmoothVelocityOn T u
  pressure_smooth : SmoothPressureOn T p
  velocity_periodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
    NSEMaxwell.Classical.divergence (u t) x = 0
  equation : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
    finiteTimeDerivative T u t x + convection (u t) x +
      NSEMaxwell.Classical.gradient (p t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x
  initial : u 0 = a
  pressure_normalized : ∀ t ∈ Icc (0 : ℝ) T, scalarMean (p t) = 0

/-- The corresponding finite-slab local Newtonian Cauchy balance. -/
structure NewtonianSolutionOn (ν : ℝ) (a : Field) (T : ℝ)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : SmoothVelocityOn T u
  pressure_smooth : SmoothPressureOn T p
  velocity_periodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
    NSEMaxwell.Classical.divergence (u t) x = 0
  momentum_balance : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
    finiteMaterialAcceleration T u t x =
      tensorDivergence (newtonianStress ν (u t) (p t)) x
  initial : u 0 = a
  pressure_normalized : ∀ t ∈ Icc (0 : ℝ) T, scalarMean (p t) = 0

/-- The scoped finite normalized-pressure equivalence target. -/
def FiniteExactEquivalence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ a : Field, Data a → ∀ u : Velocity, ∀ p : Pressure,
      (NSSolutionOn ν a T u p ↔ NewtonianSolutionOn ν a T u p)

end

end ClassicalMechanics
