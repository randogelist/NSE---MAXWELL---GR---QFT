import Mathlib

/-!
Concrete periodic Euclidean geometry, actual derivatives, means, and admissible data.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.Classical

noncomputable section

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Field := Vec → Vec
abbrev ScalarField := Vec → ℝ
abbrev Velocity := ℝ → Field
abbrev Pressure := ℝ → ScalarField
abbrev Frequency := Fin 3 → ℤ

/-- Standard unit coordinate direction. -/
def unitVector (i : Fin 3) : Vec :=
  EuclideanSpace.single i (1 : ℝ)

/-- Closed fundamental cube; boundary faces have Lebesgue measure zero. -/
def unitCube : Set Vec :=
  {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

/-- Unit periodicity in each spatial coordinate. -/
def SpatialPeriodic {E : Type*} (f : Vec → E) : Prop :=
  ∀ (x : Vec) (i : Fin 3), f (x + unitVector i) = f x

def spatialMean (a : Field) : Vec :=
  ∫ x in unitCube, a x

def scalarMean (f : ScalarField) : ℝ :=
  ∫ x in unitCube, f x

def coordinateDerivative (a : Field) (i : Fin 3) (x : Vec) : Vec :=
  fderiv ℝ a x (unitVector i)

def divergence (a : Field) (x : Vec) : ℝ :=
  ∑ i : Fin 3, coordinateDerivative a i x i

def gradient (f : ScalarField) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => fderiv ℝ f x (unitVector i))

def laplacian (a : Field) (x : Vec) : Vec :=
  ∑ i : Fin 3, fderiv ℝ (coordinateDerivative a i) x (unitVector i)

def scalarLaplacian (f : ScalarField) (x : Vec) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : Vec => fderiv ℝ f y (unitVector i)) x (unitVector i)

/-- Right-handed Euclidean cross product. -/
def cross (a b : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i = 0 then a 1 * b 2 - a 2 * b 1
    else if i = 1 then a 2 * b 0 - a 0 * b 2
    else a 0 * b 1 - a 1 * b 0)

/-- Curl in the standard right-handed coordinate frame. -/
def spatialCurl (a : Field) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i = 0 then coordinateDerivative a 1 x 2 - coordinateDerivative a 2 x 1
    else if i = 1 then coordinateDerivative a 2 x 0 - coordinateDerivative a 0 x 2
    else coordinateDerivative a 0 x 1 - coordinateDerivative a 1 x 0)

def convection (a : Field) (x : Vec) : Vec :=
  fderiv ℝ a x (a x)

/-- Right derivative at zero; ordinary derivative at positive times. -/
def timeDerivative (u : Velocity) (t : ℝ) (x : Vec) : Vec :=
  derivWithin (fun s : ℝ => u s x) (Ici (0 : ℝ)) t

def scalarTimeDerivative (f : Pressure) (t : ℝ) (x : Vec) : ℝ :=
  derivWithin (fun s : ℝ => f s x) (Ici (0 : ℝ)) t

def forwardSpacetime : Set (ℝ × Vec) :=
  {z | 0 ≤ z.1}

def SmoothPeriodic (a : Field) : Prop :=
  ContDiff ℝ ∞ a ∧ SpatialPeriodic a

def SmoothVelocity (u : Velocity) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime

def SmoothPressure (p : Pressure) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) forwardSpacetime

def PeriodicVelocity (u : Velocity) : Prop :=
  ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)

def PeriodicPressure (p : Pressure) : Prop :=
  ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (p t)

/-- Every smooth periodic divergence-free velocity datum is admissible.
There is no restriction on its spatial mean. -/
structure Data (a : Field) : Prop where
  smooth : ContDiff ℝ ∞ a
  periodic : SpatialPeriodic a
  divergence_free : ∀ x : Vec, divergence a x = 0

/-- Vorticity data belong to the divergence-free mean-zero class. -/
structure MagneticData (B₀ : Field) : Prop extends Data B₀ where
  mean_zero : spatialMean B₀ = 0

end

end NSEMaxwell.Classical
