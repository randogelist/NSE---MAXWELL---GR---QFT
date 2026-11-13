import SingularClosure.PhysicalChannels

/-!
# Actual derivatives of finite six-channel fields

This module identifies the physical Fréchet coordinate derivative with its
Fourier multiplier, and transfers the solenoidal coefficient condition to the
literal divergence operator in `Contracts`. All results concern the concrete
finite synthesis. No infinite Fourier reconstruction or integral Parseval
identity is assumed; the full frozen projection endpoint remains separate.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- The exact coefficient multiplier for the physical coordinate derivative. -/
def derivativeSymbol (j : Fin 3) (k : Frequency) : ℂ :=
  ((2 * Real.pi * (k j : ℝ) : ℝ) : ℂ) * Complex.I

/-- The phase as a continuous real-linear map, before exponentiation. -/
def fourierPhaseCLM (k : Frequency) : Vec →L[ℝ] ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k •
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j))

theorem fourierPhaseCLM_apply (k : Frequency) (x : Vec) :
    fourierPhaseCLM k x =
      ((2 * Real.pi * (∑ j : Fin 3, (k j : ℝ) * x j) : ℝ) : ℂ) * Complex.I := by
  simp only [fourierPhaseCLM, derivativeSymbol, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, EuclideanSpace.coe_proj, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fourierPhaseCLM_unitVector (k : Frequency) (j : Fin 3) :
    fourierPhaseCLM k (unitVector j) = derivativeSymbol j k := by
  simp [fourierPhaseCLM, unitVector, apply_ite, mul_ite]

theorem fourierCharacter_hasFDerivAt (k : Frequency) (x : Vec) :
    HasFDerivAt (fourierCharacter k)
      (fourierCharacter k x • fourierPhaseCLM k) x := by
  have hp : HasFDerivAt (fun y : Vec => fourierPhaseCLM k y)
      (fourierPhaseCLM k) x := (fourierPhaseCLM k).hasFDerivAt
  have hf : fourierCharacter k =
      (fun y : Vec => Complex.exp (fourierPhaseCLM k y)) := by
    funext y
    rw [fourierPhaseCLM_apply]
    rfl
  rw [hf]
  exact hp.cexp

theorem fourierCharacter_eq_exp_phase (k : Frequency) (x : Vec) :
    fourierCharacter k x = Complex.exp (fourierPhaseCLM k x) := by
  rw [fourierPhaseCLM_apply]
  rfl

theorem fourierCharacter_periodic (k : Frequency) :
    SpatialPeriodic (fourierCharacter k) := by
  intro x j
  simp only [fourierCharacter_eq_exp_phase]
  rw [map_add,
    fourierPhaseCLM_unitVector, Complex.exp_add]
  have hz : derivativeSymbol j k =
      (k j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast]
    ring
  rw [hz, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem finiteSynthesis_periodic (N : ℕ) (a : FourierCoeff) :
    SpatialPeriodic (finiteSynthesis N a) := by
  intro x j
  ext i
  change (∑ k ∈ cutoffModes N, fourierCharacter k (x + unitVector j) * a k i).re =
    (∑ k ∈ cutoffModes N, fourierCharacter k x * a k i).re
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [fourierCharacter_periodic k x j]

theorem physicalChannel_periodic (N : ℕ) (A : Fin 6) (a : FourierCoeff) :
    SpatialPeriodic (physicalChannel N A a) :=
  finiteSynthesis_periodic N (spectralChannel A a)

/-- Actual coordinate differentiation of the synthesized physical field. -/
theorem finiteSynthesis_coordinateDerivative (N : ℕ) (a : FourierCoeff)
    (j : Fin 3) :
    coordinateDerivative (finiteSynthesis N a) j =
      finiteSynthesis N (spectralMultiplier (derivativeSymbol j) a) := by
  funext x
  ext i
  have hs : HasFDerivAt
      (fun y : Vec => ∑ k ∈ cutoffModes N, fourierCharacter k y * a k i)
      (∑ k ∈ cutoffModes N,
        a k i • (fourierCharacter k x • fourierPhaseCLM k)) x := by
    exact HasFDerivAt.fun_sum fun k _ =>
      (fourierCharacter_hasFDerivAt k x).mul_const (a k i)
  have hr := Complex.reCLM.hasFDerivAt.comp x hs
  have hp := (EuclideanSpace.proj i).hasFDerivAt.comp x
    ((finiteSynthesis_contDiff N a).differentiable (by simp) x).hasFDerivAt
  have heq := hp.unique hr
  have heval := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) heq
  change (fderiv ℝ (finiteSynthesis N a) x (unitVector j)) i =
    (∑ k ∈ cutoffModes N,
      fourierCharacter k x * (derivativeSymbol j k * a k i)).re
  simpa only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj,
    Complex.reCLM_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    fourierPhaseCLM_unitVector, mul_comm, mul_left_comm, mul_assoc] using heval

/-- Physical differentiation commutes with the six diagonal coefficient masks. -/
theorem physicalChannel_coordinateDerivative (N : ℕ) (A : Fin 6)
    (a : FourierCoeff) (j : Fin 3) :
    coordinateDerivative (physicalChannel N A a) j =
      physicalChannel N A (spectralMultiplier (derivativeSymbol j) a) := by
  unfold physicalChannel
  rw [finiteSynthesis_coordinateDerivative, spectralChannel_commutes_multiplier]

/-- The first four channels are independent of the third coordinate. -/
theorem physicalChannel_first_four_third_derivative_zero
    (N : ℕ) (A : Fin 6) (hA : A.val < 4) (a : FourierCoeff) :
    coordinateDerivative (physicalChannel N A a) 2 = 0 := by
  unfold physicalChannel
  rw [finiteSynthesis_coordinateDerivative]
  have hz : spectralMultiplier (derivativeSymbol 2) (spectralChannel A a) = 0 := by
    funext k i
    fin_cases A <;>
      by_cases h2 : k 2 = 0 <;> by_cases h0 : k 0 = 0 <;>
      simp_all [spectralMultiplier, derivativeSymbol, spectralChannel, channelOf]
  rw [hz, finiteSynthesis_zero]

/-- Channels with the averaging index zero are independent of the first coordinate. -/
theorem physicalChannel_even_first_derivative_zero
    (N : ℕ) (A : Fin 6) (hA : A = 0 ∨ A = 2 ∨ A = 4) (a : FourierCoeff) :
    coordinateDerivative (physicalChannel N A a) 0 = 0 := by
  unfold physicalChannel
  rw [finiteSynthesis_coordinateDerivative]
  have hz : spectralMultiplier (derivativeSymbol 0) (spectralChannel A a) = 0 := by
    funext k i
    rcases hA with rfl | rfl | rfl <;>
      by_cases h2 : k 2 = 0 <;> by_cases h0 : k 0 = 0 <;>
      by_cases hi : i = 2 <;>
      simp [spectralMultiplier, derivativeSymbol, spectralChannel, channelOf, h0, h2, hi]
  rw [hz, finiteSynthesis_zero]

theorem finiteSynthesis_divergence_eq (N : ℕ) (a : FourierCoeff) (x : Vec) :
    divergence (finiteSynthesis N a) x =
      (∑ k ∈ cutoffModes N,
        fourierCharacter k x *
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
            (∑ i : Fin 3, (k i : ℂ) * a k i))).re := by
  unfold divergence
  simp only [finiteSynthesis_coordinateDerivative, finiteSynthesis,
    spectralMultiplier, derivativeSymbol]
  simp only [← Complex.re_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Coefficient solenoidality implies literal divergence freedom. -/
theorem finiteSynthesis_divergence_free (N : ℕ) (a : FourierCoeff)
    (ha : SpectralSolenoidal a) (x : Vec) :
    divergence (finiteSynthesis N a) x = 0 := by
  rw [finiteSynthesis_divergence_eq]
  have hs : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * a k i) = 0 := ha
  simp only [hs, mul_zero, Finset.sum_const_zero, Complex.zero_re]

theorem physicalChannel_divergence_free (N : ℕ) (A : Fin 6)
    (a : FourierCoeff) (ha : SpectralSolenoidal a) (x : Vec) :
    divergence (physicalChannel N A a) x = 0 :=
  finiteSynthesis_divergence_free N (spectralChannel A a)
    (spectralChannel_preserves_solenoidal A ha) x

/-- Every admitted concrete Galerkin trajectory has physically solenoidal channels. -/
theorem GalerkinSolution.physicalChannel_divergence_free
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) (A : Fin 6) (x : Vec) :
    divergence (physicalChannel N A (g.coeff t)) x = 0 :=
  SingularClosure.physicalChannel_divergence_free N A (g.coeff t)
    (g.solenoidal t ht) x

end

end SingularClosure
