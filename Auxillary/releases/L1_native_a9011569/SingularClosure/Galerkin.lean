import SingularClosure.Contracts
import SingularClosure.SixChannels

/-!
# Concrete Fourier--Galerkin trajectories

This file defines the actual finite-frequency NSE system.  It does not assume
or prove global existence of that system: construction and uniqueness of an
inhabitant of `GalerkinSolution` remain frozen endpoint 3.

The cutoff is the Euclidean ball `0 < |k| <= N`, not a collocation grid.
Initial coefficients are actual Fourier integrals of the physical datum.
The nonlinear convolution is followed by the modewise Leray projection.
No unspecified bilinear map, arbitrary evolution, or analytic endpoint record
is used in the definition.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure

noncomputable section

/-- Squared Euclidean integer frequency. -/
def galerkinFreqSq (k : Frequency) : ℤ :=
  ∑ i : Fin 3, (k i) ^ 2

/-- A finite enumeration of exactly the nonzero Euclidean cutoff modes. -/
def cutoffModes (N : ℕ) : Finset Frequency :=
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  (((s.product s).product s).image
    (fun q : (ℤ × ℤ) × ℤ => ![q.1.1, q.1.2, q.2])).filter
      (fun k => k ≠ 0 ∧ galerkinFreqSq k ≤ (N : ℤ) ^ 2)

/-- The standard unit-period Fourier character on the physical lift. -/
def fourierCharacter (k : Frequency) (x : Vec) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * x i) : ℝ) : ℂ) * Complex.I)

/-- Actual Fourier integrand of component `i`. -/
def datumFourierIntegrand (a : Field) (k : Frequency) (i : Fin 3)
    (x : Vec) : ℂ :=
  star (fourierCharacter k x) * (a x i : ℂ)

/-- Actual Fourier coefficient, with integrability required in the trajectory contract. -/
def datumFourierCoeff (a : Field) : FourierCoeff :=
  fun k i => ∫ x in unitCube, datumFourierIntegrand a k i x

/-- Real physical synthesis of a finite Fourier coefficient family. -/
def finiteSynthesis (N : ℕ) (c : FourierCoeff) : Field :=
  fun x => WithLp.toLp 2 (fun i : Fin 3 =>
    (∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re)

/-- The modewise Leray projection.  The zero-mode branch is never evolved. -/
def coefficientLeray (k : Frequency) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if k = 0 then v else
    fun i => v i - (k i : ℂ) * (∑ j : Fin 3, (k j : ℂ) * v j) /
      (∑ j : Fin 3, (k j : ℂ) ^ 2)

/-- Fourier coefficient of the finite convolution `(u dot grad) u`. -/
def coefficientTransport (N : ℕ) (c : FourierCoeff) (k : Frequency)
    (i : Fin 3) : ℂ :=
  ∑ p ∈ cutoffModes N,
    (∑ j : Fin 3,
      c p j * (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) *
      c (k - p) i

/-- The actual viscous, projected NSE coefficient vector field. -/
def galerkinRhs (ν : ℝ) (N : ℕ) (c : FourierCoeff)
    (k : Frequency) (i : Fin 3) : ℂ :=
  -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c k i -
    coefficientLeray k (coefficientTransport N c k) i

/-- A global trajectory of the actual finite-dimensional NSE system.

Every field below is part of the concrete equation or its real, solenoidal
state space.  None is an assumption of a compactness, continuation, or PDE
regularity theorem.  Global existence is deliberately not asserted here.
-/
structure GalerkinSolution (ν : ℝ) (a : Field) (N : ℕ) where
  coeff : ℝ → FourierCoeff
  coefficient_continuous : ∀ k : Frequency, ∀ i : Fin 3,
    ContinuousOn (fun t : ℝ => coeff t k i) (Ici 0)
  mode_support : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency,
    k ∉ cutoffModes N → ∀ i : Fin 3, coeff t k i = 0
  real_symmetry : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency, ∀ i : Fin 3,
    coeff t (-k) i = star (coeff t k i)
  solenoidal : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency,
    (∑ i : Fin 3, (k i : ℂ) * coeff t k i) = 0
  initial_integrable : ∀ k : Frequency, ∀ i : Fin 3,
    IntegrableOn (datumFourierIntegrand a k i) unitCube volume
  initial : ∀ k : Frequency, ∀ i : Fin 3,
    coeff 0 k i = if k ∈ cutoffModes N then datumFourierCoeff a k i else 0
  equation : ∀ t : ℝ, 0 ≤ t → ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
    HasDerivWithinAt (fun s : ℝ => coeff s k i)
      (galerkinRhs ν N (coeff t) k i) (Ici 0) t

/-- Physical velocity represented by the coefficient trajectory. -/
def GalerkinSolution.velocity {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) : Velocity :=
  fun t => finiteSynthesis N (g.coeff t)

theorem cutoffModes_zero_not_mem (N : ℕ) :
    (0 : Frequency) ∉ cutoffModes N := by
  simp [cutoffModes]

theorem coefficientTransport_zero (N : ℕ) (k : Frequency) :
    coefficientTransport N (0 : FourierCoeff) k = 0 := by
  funext i
  simp [coefficientTransport]

theorem coefficientLeray_zero (k : Frequency) :
    coefficientLeray k (0 : Fin 3 → ℂ) = 0 := by
  funext i
  by_cases hk : k = 0 <;> simp [coefficientLeray, hk]

theorem galerkinRhs_zero (ν : ℝ) (N : ℕ) (k : Frequency) :
    galerkinRhs ν N (0 : FourierCoeff) k = 0 := by
  funext i
  simp [galerkinRhs, coefficientTransport_zero, coefficientLeray_zero]

theorem finiteSynthesis_zero (N : ℕ) :
    finiteSynthesis N (0 : FourierCoeff) = 0 := by
  funext x
  ext i
  simp [finiteSynthesis]

/-- A genuine zero-data trajectory; this does not discharge endpoint 3 for general data. -/
def zeroGalerkinSolution (ν : ℝ) (N : ℕ) : GalerkinSolution ν (0 : Field) N where
  coeff := fun _ => 0
  coefficient_continuous := by
    intro k i
    exact continuousOn_const
  mode_support := by
    intro t ht k hk i
    rfl
  real_symmetry := by
    intro t ht k i
    simp
  solenoidal := by
    intro t ht k
    simp
  initial_integrable := by
    intro k i
    have hz : datumFourierIntegrand (0 : Field) k i =
        (fun _ : Vec => (0 : ℂ)) := by
      funext x
      simp [datumFourierIntegrand]
    rw [hz]
    exact integrableOn_zero
  initial := by
    intro k i
    simp [datumFourierCoeff, datumFourierIntegrand]
  equation := by
    intro t ht k hk i
    change HasDerivWithinAt (fun _ : ℝ => (0 : ℂ))
      (galerkinRhs ν N (0 : FourierCoeff) k i) (Ici 0) t
    rw [galerkinRhs_zero]
    exact (hasDerivAt_const t (0 : ℂ)).hasDerivWithinAt

theorem zeroGalerkinSolution_velocity (ν : ℝ) (N : ℕ) :
    (zeroGalerkinSolution ν N).velocity = (0 : Velocity) := by
  funext t
  exact finiteSynthesis_zero N

end

end SingularClosure
