import Mathlib

/-!
# Concrete periodic Navier–Stokes and constrained Maxwell statements

The spatial domain is represented by unit-periodic lifts on real Euclidean
three-space. Differential operators are Mathlib derivatives; means are actual
Lebesgue integrals. Smoothness has order `∞`, including the boundary `t = 0`.

`vectorL` and `scalarL` are the actual real Fourier cosine formulas for the
mean-zero inverse of `-Δ`. The formulas are total definitions. Their convergence,
Poisson identities, and smooth parameter dependence are analytic obligations;
no such result is assumed by these definitions.

This module defines the exact propositions. It does not prove their equivalence
or either existence assertion.
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

/-- The zero Fourier mode is removed from the inverse Laplacian. -/
def inverseLaplacianSymbol (k : Frequency) : ℝ :=
  if k = 0 then 0
  else (4 * Real.pi ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2))⁻¹

def cosineKernel (k : Frequency) (x y : Vec) : ℝ :=
  Real.cos (2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * (x i - y i)))

/-- Real Fourier formula for the vector mean-zero inverse of `-Δ`.
For smooth periodic inputs, convergence and inversion require proof. -/
def vectorL (a : Field) (x : Vec) : Vec :=
  ∑' k : Frequency,
    inverseLaplacianSymbol k •
      (∫ y in unitCube, cosineKernel k x y • a y)

/-- Scalar version of the same canonical Fourier operator. -/
def scalarL (f : ScalarField) (x : Vec) : ℝ :=
  ∑' k : Frequency,
    inverseLaplacianSymbol k *
      (∫ y in unitCube, cosineKernel k x y * f y)

def K (B : Field) : Field :=
  spatialCurl (vectorL B)

def U (m : Vec) (B : Field) : Field :=
  fun x => m + K B x

def G (ν : ℝ) (m : Vec) (B : Field) : Field :=
  fun x => cross (B x) (U m B x) + ν • spatialCurl B x

def V (ν : ℝ) (m : Vec) (B : Field) : Field :=
  fun x => -spatialCurl (G ν m B) x

def Q (ν : ℝ) (m : Vec) (B : Field) : ScalarField :=
  divergence (G ν m B)

/-- Explicit differential of the constitutive electric-field map. -/
def DG (ν : ℝ) (m : Vec) (B h : Field) : Field :=
  fun x => cross (h x) (U m B x) + cross (B x) (K h x) +
    ν • spatialCurl h x

def current (ν c : ℝ) (m : Vec) (B : Field) : Field :=
  fun x => c ^ 2 • spatialCurl B x - DG ν m B (V ν m B) x

/-- The mean-zero canonical pressure selected by the B-tier derivation. -/
def canonicalPressure (ν : ℝ) (m : Vec) (B : Field) : ScalarField :=
  fun x => scalarL (Q ν m B) x - ‖U m B x‖ ^ 2 / 2 +
    scalarMean (fun y => ‖U m B y‖ ^ 2) / 2

def canonicalVelocity (m : Vec) (B : Velocity) : Velocity :=
  fun t => U m (B t)

def canonicalElectric (ν : ℝ) (m : Vec) (B : Velocity) : Velocity :=
  fun t => G ν m (B t)

def canonicalCharge (ν : ℝ) (m : Vec) (B : Velocity) : Pressure :=
  fun t => Q ν m (B t)

def canonicalCurrent (ν c : ℝ) (m : Vec) (B : Velocity) : Velocity :=
  fun t => current ν c m (B t)

def canonicalPressureTrajectory (ν : ℝ) (m : Vec) (B : Velocity) : Pressure :=
  fun t => canonicalPressure ν m (B t)

/-- Classical unforced periodic NSE, at every nonnegative time.
Pressure is periodic; arbitrary velocity means and pressure gauges are allowed. -/
structure NSSolution (ν : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : SmoothVelocity u
  pressure_smooth : SmoothPressure p
  velocity_periodic : PeriodicVelocity u
  pressure_periodic : PeriodicPressure p
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + gradient (p t) x =
      ν • laplacian (u t) x
  initial : u 0 = a

/-- Constrained Maxwell system with precisely the induced electric field,
charge, and current. Only `m` and `B₀` are independent initial data. -/
structure MaxwellSolution (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity) : Prop where
  magnetic_smooth : SmoothVelocity B
  electric_smooth : SmoothVelocity E
  charge_smooth : SmoothPressure ρ
  current_smooth : SmoothVelocity J
  magnetic_periodic : PeriodicVelocity B
  electric_periodic : PeriodicVelocity E
  charge_periodic : PeriodicPressure ρ
  current_periodic : PeriodicVelocity J
  magnetic_mean_zero : ∀ t : ℝ, 0 ≤ t → spatialMean (B t) = 0
  magnetic_gauss : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (B t) x = 0
  faraday : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative B t x + spatialCurl (E t) x = 0
  electric_gauss : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    divergence (E t) x = ρ t x
  ampere : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative E t x - c ^ 2 • spatialCurl (B t) x = -J t x
  constitutive_electric : ∀ t : ℝ, 0 ≤ t → E t = G ν m (B t)
  constitutive_charge : ∀ t : ℝ, 0 ≤ t → ρ t = Q ν m (B t)
  constitutive_current : ∀ t : ℝ, 0 ≤ t → J t = current ν c m (B t)
  initial : B 0 = B₀

/-- Fefferman's periodic unforced existence proposition for fixed viscosity. -/
def FeffermanB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a →
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p

/-- Global constrained-Maxwell existence for arbitrary mean and magnetic datum. -/
def MaxwellB (ν c : ℝ) : Prop :=
  ∀ (m : Vec) (B₀ : Field), MagneticData B₀ →
    ∃ (B E : Velocity) (ρ : Pressure) (J : Velocity),
      MaxwellSolution ν c m B₀ B E ρ J

/-- The requested unconditional proposition. This declaration is not a proof. -/
def ExactEquivalence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
    (FeffermanB ν ↔ MaxwellB ν c)

end

end NSEMaxwell.Classical
