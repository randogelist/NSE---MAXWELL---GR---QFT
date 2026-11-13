import SingularClosure.Galerkin

/-!
# The single proposed analytic admission

`AX6Statement` is a proposition, not an axiom declaration and not a proved
theorem.  It concerns the concrete finite Fourier--Galerkin equations from
`Galerkin.lean`.  It does not assume a global solution of the infinite NSE.

The universal-trajectory formulation avoids selecting a Galerkin trajectory
before endpoint 3 has proved its existence and uniqueness.  Equivalence with
the canonical-trajectory formulation is an explicit future consequence of
that endpoint; it must not be silently assumed.

Both spatial and temporal integrals are nonnegative extended integrals.
Thus an integrability failure cannot turn an intended positive integral into
zero through totalization.  The right-hand bound is the coercion of a finite
nonnegative real number and is independent of the cutoff N.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SingularClosure

noncomputable section

/-- The actual squared gradient density of a physical vector field. -/
def gradientSquareDensity (v : Field) (x : Vec) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (coordinateDerivative v i x j) ^ 2

/-- Physical enstrophy, as an extended nonnegative integral. -/
def physicalEnstrophy (v : Field) : ℝ≥0∞ :=
  ∫⁻ x in unitCube, ENNReal.ofReal (gradientSquareDensity v x)

/-- Sum of the six physical channel enstrophies for finite synthesis. -/
def sixEnstrophy (N : ℕ) (c : FourierCoeff) : ℝ≥0∞ :=
  ∑ A : Fin 6, physicalEnstrophy (finiteSynthesis N (spectralChannel A c))

/-- The finite-time square-enstrophy budget. -/
def budget6 (N : ℕ) (c : ℝ → FourierCoeff) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) T, (sixEnstrophy N (c t)) ^ 2

/-- The proposed single analytic premise, with all physical data explicit.

M may depend on viscosity, datum and finite time, but not on N or a chosen
trajectory.  `GalerkinSolution` existence is a separate ordinary theorem to
be proved at frozen endpoint 3; no axiom for it is introduced in this file.
-/
def AX6Statement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : Field), SmoothSigmaZero a →
    ∀ (T : ℝ), 0 < T → ∃ M : ℝ≥0,
      ∀ (N : ℕ), 1 ≤ N → ∀ g : GalerkinSolution ν a N,
        budget6 N g.coeff T ≤ (M : ℝ≥0∞)

theorem gradientSquareDensity_nonneg (v : Field) (x : Vec) :
    0 ≤ gradientSquareDensity v x := by
  unfold gradientSquareDensity
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg (coordinateDerivative v i x j)))

/-- Axiom finiteness is actual finiteness in the extended nonnegative reals. -/
theorem budget6_ne_top_of_bound
    {N : ℕ} {c : ℝ → FourierCoeff} {T : ℝ} {M : ℝ≥0}
    (h : budget6 N c T ≤ (M : ℝ≥0∞)) :
    budget6 N c T ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top h

end

end SingularClosure
