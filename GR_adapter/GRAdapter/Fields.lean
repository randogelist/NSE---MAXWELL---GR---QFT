import Mathlib

/-!
# Actual local analytic periodic NSE fields

The temporal derivative is the ordinary derivative on a two-sided open
interval. The Poisson and Leray formulas are concrete total integral/series
expressions. Their convergence, inversion, and analytic mapping properties
are not assumed or proved by their definitions.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEGR

noncomputable section

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Field := Vec → Vec
abbrev ScalarField := Vec → ℝ
abbrev Velocity := ℝ → Field
abbrev Pressure := ℝ → ScalarField
abbrev Frequency := Fin 3 → ℤ
abbrev TensorField := Vec → Matrix (Fin 3) (Fin 3) ℝ

def unitVector (i : Fin 3) : Vec :=
  EuclideanSpace.single i (1 : ℝ)

def unitCube : Set Vec :=
  {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

def SpatialPeriodic {E : Type*} (f : Vec → E) : Prop :=
  ∀ (x : Vec) (i : Fin 3), f (x + unitVector i) = f x

def spatialMean (a : Field) : Vec := ∫ x in unitCube, a x

def scalarMean (f : ScalarField) : ℝ := ∫ x in unitCube, f x

def spatialPartial (a : Field) (i : Fin 3) (x : Vec) : Vec :=
  fderiv ℝ a x (unitVector i)

def gradient (f : ScalarField) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => fderiv ℝ f x (unitVector i))

def divergence (a : Field) (x : Vec) : ℝ :=
  ∑ i : Fin 3, spatialPartial a i x i

def laplacian (a : Field) (x : Vec) : Vec :=
  ∑ i : Fin 3, fderiv ℝ (spatialPartial a i) x (unitVector i)

def scalarLaplacian (f : ScalarField) (x : Vec) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : Vec => fderiv ℝ f y (unitVector i)) x (unitVector i)

def scalarHessian (f : ScalarField) (x : Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    fderiv ℝ (fun y : Vec => fderiv ℝ f y (unitVector j)) x (unitVector i)

def strain (a : Field) (x : Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => spatialPartial a i x j + spatialPartial a j x i

def tensorDivergence (F : TensorField) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    ∑ j : Fin 3, fderiv ℝ (fun y : Vec => F y i j) x (unitVector j))

def convection (a : Field) (x : Vec) : Vec :=
  fderiv ℝ a x (a x)

/-- Ordinary two-sided temporal derivative; no `Ici 0` derivative convention. -/
def localTimeDerivative (u : Velocity) (t : ℝ) (x : Vec) : Vec :=
  deriv (fun s : ℝ => u s x) t

def scalarLocalTimeDerivative (p : Pressure) (t : ℝ) (x : Vec) : ℝ :=
  deriv (fun s : ℝ => p s x) t

def nseResidual (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec) : Vec :=
  localTimeDerivative u t x + convection (u t) x + gradient (p t) x -
    ν • laplacian (u t) x

def timeInterval (t0 δ : ℝ) : Set ℝ := Ioo (t0 - δ) (t0 + δ)

def spacetimeSlab (t0 δ : ℝ) : Set (ℝ × Vec) :=
  {z | z.1 ∈ timeInterval t0 δ}

/-- Actual jointly analytic periodic representatives on a full spatial slab. -/
structure AnalyticPeriodicPair (t0 δ : ℝ) (u : Velocity) (p : Pressure) : Prop where
  radius_pos : 0 < δ
  velocity_analytic : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2)
    (spacetimeSlab t0 δ)
  pressure_analytic : AnalyticOnNhd ℝ (fun z : ℝ × Vec => p z.1 z.2)
    (spacetimeSlab t0 δ)
  periodic_velocity : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (u t)
  periodic_pressure : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (p t)

/-- Local analytic NSE; arbitrary velocity mean, no global existence assertion. -/
structure LocalNSE (ν t0 δ : ℝ) (u : Velocity) (p : Pressure) : Prop
    extends AnalyticPeriodicPair t0 δ u p where
  divergence_free : ∀ t ∈ timeInterval t0 δ, ∀ x, divergence (u t) x = 0
  momentum : ∀ t ∈ timeInterval t0 δ, ∀ x, nseResidual ν u p t x = 0

/-- Mean-zero inverse symbol for `Delta`, with the zero frequency removed. -/
def poissonSymbol (k : Frequency) : ℝ :=
  if k = 0 then 0
  else -(4 * Real.pi ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2))⁻¹

def cosineKernel (k : Frequency) (x y : Vec) : ℝ :=
  Real.cos (2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * (x i - y i)))

/-- Actual cosine integral series. Inversion requires an independent proof. -/
def poissonInverse (f : ScalarField) (x : Vec) : ℝ :=
  ∑' k : Frequency,
    poissonSymbol k * (∫ y in unitCube, cosineKernel k x y * f y)

/-- Actual Helmholtz formula, retaining the input constant vector mode. -/
def leray (a : Field) (x : Vec) : Vec :=
  a x - gradient (poissonInverse (divergence a)) x

/-- Symmetry is an exact property of the actual first-derivative formula. -/
theorem strain_symmetric (a : Field) (x : Vec) :
    (strain a x).transpose = strain a x := by
  ext i j
  simp [strain, add_comm]

/-- The trace-free strain property uses the actual divergence definition. -/
theorem trace_strain (a : Field) (x : Vec) :
    Matrix.trace (strain a x) = 2 * divergence a x := by
  simp only [Matrix.trace, strain, divergence, Finset.sum_add_distrib]
  ring

theorem trace_strain_eq_zero (a : Field) (x : Vec) (h : divergence a x = 0) :
    Matrix.trace (strain a x) = 0 := by
  rw [trace_strain, h, mul_zero]

@[simp] theorem spatialMean_zero : spatialMean (0 : Field) = 0 := by
  simp [spatialMean]

@[simp] theorem scalarMean_zero : scalarMean (0 : ScalarField) = 0 := by
  simp [scalarMean]

theorem spatialPeriodic_const {E : Type*} (c : E) :
    SpatialPeriodic (fun _ : Vec => c) := by
  intro x i
  rfl

@[simp] theorem spatialPartial_const (c : Vec) (i : Fin 3) :
    spatialPartial (fun _ : Vec => c) i = 0 := by
  funext x
  simp [spatialPartial]

@[simp] theorem gradient_const (c : ℝ) :
    gradient (fun _ : Vec => c) = 0 := by
  funext x
  apply PiLp.ext
  intro i
  simp [gradient, PiLp.toLp_apply]

@[simp] theorem divergence_const (c : Vec) :
    divergence (fun _ : Vec => c) = 0 := by
  funext x
  simp [divergence]

@[simp] theorem laplacian_const (c : Vec) :
    laplacian (fun _ : Vec => c) = 0 := by
  funext x
  simp [laplacian]

@[simp] theorem scalarLaplacian_const (c : ℝ) :
    scalarLaplacian (fun _ : Vec => c) = 0 := by
  funext x
  simp [scalarLaplacian]

@[simp] theorem scalarHessian_const (c : ℝ) :
    scalarHessian (fun _ : Vec => c) = 0 := by
  funext x i j
  simp [scalarHessian]

@[simp] theorem strain_const (c : Vec) :
    strain (fun _ : Vec => c) = 0 := by
  funext x i j
  simp [strain]

@[simp] theorem tensorDivergence_const (C : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorDivergence (fun _ : Vec => C) = 0 := by
  funext x
  apply PiLp.ext
  intro i
  simp [tensorDivergence, PiLp.toLp_apply]

@[simp] theorem convection_const (c : Vec) :
    convection (fun _ : Vec => c) = 0 := by
  funext x
  simp [convection]

@[simp] theorem localTimeDerivative_const (c : Vec) :
    localTimeDerivative (fun _ _ => c) = 0 := by
  funext t x
  simp [localTimeDerivative]

@[simp] theorem scalarLocalTimeDerivative_const (c : ℝ) :
    scalarLocalTimeDerivative (fun _ _ => c) = 0 := by
  funext t x
  simp [scalarLocalTimeDerivative]

@[simp] theorem nseResidual_const (ν : ℝ) (m : Vec) (c : ℝ) :
    nseResidual ν (fun _ _ => m) (fun _ _ => c) = 0 := by
  funext t x
  simp [nseResidual]

@[simp] theorem poissonSymbol_zero : poissonSymbol (0 : Frequency) = 0 := by
  simp [poissonSymbol]

@[simp] theorem poissonInverse_zero : poissonInverse (0 : ScalarField) = 0 := by
  funext x
  simp [poissonInverse]

@[simp] theorem leray_const (c : Vec) :
    leray (fun _ : Vec => c) = (fun _ : Vec => c) := by
  funext x
  simp [leray]

@[simp] theorem leray_zero : leray (0 : Field) = 0 := by
  simpa using leray_const (0 : Vec)

/-- The representative-level local PDE carrier has genuine constant solutions. -/
theorem localNSE_const (ν t0 δ : ℝ) (hδ : 0 < δ) (m : Vec) (c : ℝ) :
    LocalNSE ν t0 δ (fun _ _ => m) (fun _ _ => c) where
  radius_pos := hδ
  velocity_analytic := analyticOnNhd_const
  pressure_analytic := analyticOnNhd_const
  periodic_velocity := by intro t ht; exact spatialPeriodic_const m
  periodic_pressure := by intro t ht; exact spatialPeriodic_const c
  divergence_free := by intro t ht x; simp
  momentum := by intro t ht x; simp

theorem localNSE_zero (ν t0 δ : ℝ) (hδ : 0 < δ) :
    LocalNSE ν t0 δ (0 : Velocity) (0 : Pressure) := by
  simpa using localNSE_const ν t0 δ hδ (0 : Vec) (0 : ℝ)

/-- No time regularity or PDE condition is inferred from a total operator formula. -/
theorem poissonInverse_definition (f : ScalarField) (x : Vec) :
    poissonInverse f x = ∑' k : Frequency,
      poissonSymbol k * (∫ y in unitCube, cosineKernel k x y * f y) := rfl

theorem leray_definition (a : Field) (x : Vec) :
    leray a x = a x - gradient (poissonInverse (divergence a)) x := rfl

end

end NSEGR
