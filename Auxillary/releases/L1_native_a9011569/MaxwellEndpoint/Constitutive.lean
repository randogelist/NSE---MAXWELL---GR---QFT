import MaxwellEndpoint.Geometry

/-!
Concrete Fourier operators and constrained-Maxwell constitutive fields.
The total formulas do not assert convergence, Hodge inversion, or regularity.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.Classical

noncomputable section

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

end

end NSEMaxwell.Classical
