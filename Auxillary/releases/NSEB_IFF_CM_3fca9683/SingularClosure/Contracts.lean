import Mathlib

/-!
# Concrete periodic Navier--Stokes contract

The torus is represented by unit-periodic lifts on real Euclidean three-space.
All differential operators below are the actual Mathlib derivatives, and all
means are actual Lebesgue integrals over the unit cube.  No analytic endpoint
record, arbitrary regularity predicate, or new axiom is introduced here.

`ContDiff` order `∞` means smoothness of every finite order.  It is deliberately
not order `ω` (analyticity).  At time zero the equation uses the derivative
within the nonnegative half-line, consistently with smoothness up to that
boundary.  The equation is required at every nonnegative time.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Field := Vec → Vec
abbrev Velocity := ℝ → Field
abbrev Pressure := ℝ → Vec → ℝ

/-- The standard unit coordinate direction. -/
def unitVector (i : Fin 3) : Vec :=
  EuclideanSpace.single i (1 : ℝ)

/-- The closed fundamental cube; its boundary has Lebesgue measure zero. -/
def unitCube : Set Vec :=
  {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

/-- Unit periodicity in each coordinate, for an arbitrary codomain. -/
def SpatialPeriodic {E : Type*} (f : Vec → E) : Prop :=
  ∀ (x : Vec) (i : Fin 3), f (x + unitVector i) = f x

/-- The actual vector-valued Lebesgue integral over the unit-volume cube. -/
def spatialMean (a : Field) : Vec :=
  ∫ x in unitCube, a x

/-- Explicit integrability prevents reliance on a totalized Bochner integral. -/
def MeanZero (a : Field) : Prop :=
  IntegrableOn a unitCube volume ∧ spatialMean a = 0

/-- The scalar analogue fixes the otherwise arbitrary pressure constant. -/
def PressureMeanZero (p : Vec → ℝ) : Prop :=
  IntegrableOn p unitCube volume ∧ (∫ x in unitCube, p x) = 0

/-- A first spatial coordinate derivative of a vector field. -/
def coordinateDerivative (a : Field) (i : Fin 3) (x : Vec) : Vec :=
  fderiv ℝ a x (unitVector i)

/-- The trace of the actual spatial derivative. -/
def divergence (a : Field) (x : Vec) : ℝ :=
  ∑ i : Fin 3, coordinateDerivative a i x i

/-- The Euclidean gradient of a scalar pressure. -/
def gradient (p : Vec → ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => fderiv ℝ p x (unitVector i))

/-- The componentwise Euclidean Laplacian, as a sum of second derivatives. -/
def laplacian (a : Field) (x : Vec) : Vec :=
  ∑ i : Fin 3, fderiv ℝ (coordinateDerivative a i) x (unitVector i)

/-- The actual convection term `(a dot grad) a`. -/
def convection (a : Field) (x : Vec) : Vec :=
  fderiv ℝ a x (a x)

/-- The right-hand time derivative at zero and the ordinary derivative later. -/
def timeDerivative (u : Velocity) (t : ℝ) (x : Vec) : Vec :=
  derivWithin (fun s : ℝ => u s x) (Ici (0 : ℝ)) t

/-- The closed nonnegative-time spacetime domain. -/
def forwardSpacetime : Set (ℝ × Vec) :=
  {z | 0 ≤ z.1}

/-- Concrete smooth, periodic, divergence-free, mean-zero initial data. -/
structure SmoothSigmaZero (a : Field) : Prop where
  smooth : ContDiff ℝ ∞ a
  periodic : SpatialPeriodic a
  divergence_free : ∀ x : Vec, divergence a x = 0
  mean_zero : MeanZero a

/-- A concrete global smooth solution of the unforced periodic NSE.

Both pressure normalization and preservation of the velocity mean are stated
explicitly.  This predicate contains no assumption about the availability of
solutions and no unspecified analytic adapter.
-/
structure GlobalSmoothNSE (ν : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) forwardSpacetime
  velocity_periodic : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)
  pressure_periodic : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (p t)
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + gradient (p t) x =
      ν • laplacian (u t) x
  initial : u 0 = a
  velocity_mean_zero : ∀ t : ℝ, 0 ≤ t → MeanZero (u t)
  pressure_mean_zero : ∀ t : ℝ, 0 ≤ t → PressureMeanZero (p t)

/-- The frozen adjusted periodic existence statement, with no smallness bound.

This declaration is a definition of the target proposition, not its proof.
-/
def Fefferman_B_0_adjust : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ a : Field, SmoothSigmaZero a →
    ∃ (u : Velocity) (p : Pressure), GlobalSmoothNSE ν a u p

/-- The contract admits the genuine zero datum. -/
theorem smoothSigmaZero_zero : SmoothSigmaZero (0 : Field) := by
  refine ⟨contDiff_const, ?_, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [divergence, coordinateDerivative]
  · exact ⟨integrableOn_zero, by simp [spatialMean]⟩

/-- A concrete sanity witness; it makes no assertion about nonzero data. -/
theorem globalSmoothNSE_zero (ν : ℝ) :
    GlobalSmoothNSE ν (0 : Field) (0 : Velocity) (0 : Pressure) := by
  refine ⟨contDiffOn_const, contDiffOn_const, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro t ht x i
    rfl
  · intro t ht x i
    rfl
  · intro t ht x
    simp [divergence, coordinateDerivative]
  · intro t ht x
    have hDerivative (i : Fin 3) : coordinateDerivative (0 : Field) i = 0 := by
      funext y
      simp [coordinateDerivative]
    have hGradient : gradient (0 : Vec → ℝ) x = 0 := by
      ext i
      change (fderiv ℝ (0 : Vec → ℝ) x) (unitVector i) = 0
      simp
    change timeDerivative (0 : Velocity) t x + convection (0 : Field) x +
      gradient (0 : Vec → ℝ) x = ν • laplacian (0 : Field) x
    simp [timeDerivative, convection, hGradient, laplacian, hDerivative]
  · intro t ht
    exact ⟨integrableOn_zero, by simp [spatialMean]⟩
  · intro t ht
    exact ⟨integrableOn_zero, by simp⟩

end

end SingularClosure
