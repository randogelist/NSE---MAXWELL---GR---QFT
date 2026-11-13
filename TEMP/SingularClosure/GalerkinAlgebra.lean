import SingularClosure.Galerkin

/-!
# Finite-state algebra for the concrete Galerkin equation

Restriction and zero extension identify the supported coefficient families
with a genuinely finite-dimensional space.  The vector field below is the
explicit NSE vector field from `Galerkin.lean`, restricted to that space.

These identities support frozen endpoints 3 and 4.  They do not assert
global existence, uniqueness, or nonlinear energy cancellation.
-/

set_option autoImplicit false

open Set
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Projection onto the nonzero Euclidean cutoff modes. -/
def cutoffCoeff (N : ℕ) (c : FourierCoeff) : FourierCoeff :=
  fun k i => if k ∈ cutoffModes N then c k i else 0

theorem cutoffCoeff_apply_of_mem {N : ℕ} (c : FourierCoeff)
    {k : Frequency} (hk : k ∈ cutoffModes N) (i : Fin 3) :
    cutoffCoeff N c k i = c k i := by
  simp [cutoffCoeff, hk]

theorem cutoffCoeff_apply_of_not_mem {N : ℕ} (c : FourierCoeff)
    {k : Frequency} (hk : k ∉ cutoffModes N) (i : Fin 3) :
    cutoffCoeff N c k i = 0 := by
  simp [cutoffCoeff, hk]

theorem cutoffCoeff_idempotent (N : ℕ) (c : FourierCoeff) :
    cutoffCoeff N (cutoffCoeff N c) = cutoffCoeff N c := by
  funext k i
  by_cases hk : k ∈ cutoffModes N <;> simp [cutoffCoeff, hk]

theorem cutoffCoeff_zero (N : ℕ) :
    cutoffCoeff N (0 : FourierCoeff) = 0 := by
  funext k i
  simp [cutoffCoeff]

theorem cutoffCoeff_commutes_spectralChannel (N : ℕ) (A : Fin 6)
    (c : FourierCoeff) :
    cutoffCoeff N (spectralChannel A c) =
      spectralChannel A (cutoffCoeff N c) := by
  funext k i
  by_cases hk : k ∈ cutoffModes N <;>
    by_cases hA : channelOf k i = A <;>
      simp [cutoffCoeff, spectralChannel, hk, hA]

theorem finiteSynthesis_cutoffCoeff (N : ℕ) (c : FourierCoeff) :
    finiteSynthesis N (cutoffCoeff N c) = finiteSynthesis N c := by
  funext x
  ext i
  change (∑ k ∈ cutoffModes N,
      fourierCharacter k x * cutoffCoeff N c k i).re =
    (∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [cutoffCoeff_apply_of_mem c hk i]

/-- Actual finite-dimensional complex coefficient space. -/
abbrev FiniteGalerkinState (N : ℕ) :=
  ↥(cutoffModes N) → Fin 3 → ℂ

/-- Restriction to the enumerated Euclidean cutoff. -/
def restrictFiniteState (N : ℕ) (c : FourierCoeff) : FiniteGalerkinState N :=
  fun k i => c k.val i

/-- Extension by zero to all integer frequencies. -/
def extendFiniteState (N : ℕ) (z : FiniteGalerkinState N) : FourierCoeff :=
  fun k i => if hk : k ∈ cutoffModes N then z ⟨k, hk⟩ i else 0

theorem restrict_extendFiniteState (N : ℕ) (z : FiniteGalerkinState N) :
    restrictFiniteState N (extendFiniteState N z) = z := by
  funext k i
  simp [restrictFiniteState, extendFiniteState, k.property]

theorem extend_restrictFiniteState (N : ℕ) (c : FourierCoeff) :
    extendFiniteState N (restrictFiniteState N c) = cutoffCoeff N c := by
  funext k i
  by_cases hk : k ∈ cutoffModes N <;>
    simp [extendFiniteState, restrictFiniteState, cutoffCoeff, hk]

theorem extendFiniteState_zero (N : ℕ) :
    extendFiniteState N (0 : FiniteGalerkinState N) = 0 := by
  funext k i
  simp [extendFiniteState]

theorem extendFiniteState_injective (N : ℕ) :
    Function.Injective (extendFiniteState N) := by
  intro z w h
  have hr := congrArg (restrictFiniteState N) h
  simpa only [restrict_extendFiniteState] using hr

/-- The explicit finite-dimensional NSE ODE vector field. -/
def finiteGalerkinRhs (ν : ℝ) (N : ℕ) (z : FiniteGalerkinState N) :
    FiniteGalerkinState N :=
  fun k i => galerkinRhs ν N (extendFiniteState N z) k.val i

theorem finiteGalerkinRhs_zero (ν : ℝ) (N : ℕ) :
    finiteGalerkinRhs ν N (0 : FiniteGalerkinState N) = 0 := by
  funext k i
  simp [finiteGalerkinRhs, extendFiniteState_zero, galerkinRhs_zero]

/-- Every admitted trajectory actually lies in the finite coefficient space. -/
theorem GalerkinSolution.cutoffCoeff_eq {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t) :
    cutoffCoeff N (g.coeff t) = g.coeff t := by
  funext k i
  by_cases hk : k ∈ cutoffModes N
  · exact cutoffCoeff_apply_of_mem (g.coeff t) hk i
  · rw [cutoffCoeff_apply_of_not_mem (g.coeff t) hk i]
    exact (g.mode_support t ht k hk i).symm

/-- Restriction followed by extension recovers a trajectory at nonnegative time. -/
theorem GalerkinSolution.extend_restrict_coeff {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t) :
    extendFiniteState N (restrictFiniteState N (g.coeff t)) = g.coeff t := by
  rw [extend_restrictFiniteState, g.cutoffCoeff_eq t ht]

/-- The trajectory equation is precisely the finite-state NSE ODE. -/
theorem GalerkinSolution.finite_equation {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t)
    (k : ↥(cutoffModes N)) (i : Fin 3) :
    HasDerivWithinAt
      (fun s : ℝ => restrictFiniteState N (g.coeff s) k i)
      (finiteGalerkinRhs ν N (restrictFiniteState N (g.coeff t)) k i)
      (Ici 0) t := by
  change HasDerivWithinAt (fun s : ℝ => g.coeff s k.val i)
    (galerkinRhs ν N (extendFiniteState N (restrictFiniteState N (g.coeff t)))
      k.val i) (Ici 0) t
  rw [g.extend_restrict_coeff t ht]
  exact g.equation t ht k.val k.property i

/-- Each zero-extended coefficient is a smooth finite-state coordinate map. -/
theorem contDiff_extendFiniteState_apply
    (N : ℕ) (k : Frequency) (i : Fin 3) :
    ContDiff ℝ ∞
      (fun z : FiniteGalerkinState N => extendFiniteState N z k i) := by
  classical
  unfold extendFiniteState
  split_ifs with hk
  · exact contDiff_apply_apply ℝ ℂ (⟨k, hk⟩ : ↥(cutoffModes N)) i
  · exact contDiff_const

/-- The fixed-frequency Leray map is smooth, including its unused zero branch. -/
theorem contDiff_coefficientLeray (k : Frequency) :
    ContDiff ℝ ∞ (coefficientLeray k) := by
  classical
  by_cases hk : k = 0
  · subst k
    change ContDiff ℝ ∞ (fun v : Fin 3 → ℂ => v)
    exact contDiff_id
  · apply contDiff_pi.2
    intro i
    simp only [coefficientLeray, hk, if_false]
    apply (contDiff_apply ℝ ℂ i).sub
    apply ContDiff.div_const
    apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro j hj
    exact contDiff_const.mul (contDiff_apply ℝ ℂ j)

/-- The finite Fourier convolution is polynomial, hence smooth. -/
theorem contDiff_finiteTransport (N : ℕ) (k : Frequency) :
    ContDiff ℝ ∞
      (fun z : FiniteGalerkinState N =>
        coefficientTransport N (extendFiniteState N z) k) := by
  classical
  apply contDiff_pi.2
  intro i
  unfold coefficientTransport
  apply ContDiff.sum
  intro p hp
  apply ContDiff.mul
  · apply ContDiff.sum
    intro j hj
    exact (contDiff_extendFiniteState_apply N p j).mul contDiff_const
  · exact contDiff_extendFiniteState_apply N (k - p) i

/-- The actual finite-dimensional NSE vector field is smooth. -/
theorem contDiff_finiteGalerkinRhs (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (finiteGalerkinRhs ν N) := by
  classical
  apply contDiff_pi.2
  intro k
  apply contDiff_pi.2
  intro i
  change ContDiff ℝ ∞
    (fun z : FiniteGalerkinState N =>
      galerkinRhs ν N (extendFiniteState N z) k.val i)
  unfold galerkinRhs
  apply ContDiff.sub
  · exact contDiff_const.mul
      (contDiff_extendFiniteState_apply N k.val i)
  · exact contDiff_pi.1
      ((contDiff_coefficientLeray k.val).comp
        (contDiff_finiteTransport N k.val)) i

/-- The finite coefficient energy; physical Parseval identification is separate. -/
def coefficientEnergy (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3, Complex.normSq (c k i)

theorem coefficientEnergy_nonneg (N : ℕ) (c : FourierCoeff) :
    0 ≤ coefficientEnergy N c := by
  unfold coefficientEnergy
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact sq_nonneg ‖c k i‖

theorem coefficientEnergy_zero (N : ℕ) :
    coefficientEnergy N (0 : FourierCoeff) = 0 := by
  simp [coefficientEnergy]

/-- Real differentiation of the actual complex modulus square. -/
theorem hasDerivWithinAt_complex_normSq
    {f : ℝ → ℂ} {f' : ℂ} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun r => Complex.normSq (f r))
      (2 * (star (f t) * f').re) s t := by
  simpa only [Complex.normSq_eq_norm_sq, Complex.inner, Complex.star_def,
    mul_comm] using hf.norm_sq

/-- Exact differentiation before proving the nonlinear energy cancellation. -/
theorem GalerkinSolution.coefficientEnergy_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientEnergy N (g.coeff r))
      (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        2 * (star (g.coeff t k i) * galerkinRhs ν N (g.coeff t) k i).re)
      (Ici 0) t := by
  unfold coefficientEnergy
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.fun_sum
  intro i hi
  exact hasDerivWithinAt_complex_normSq (g.equation t ht k hk i)

/-- Leray projection drops out of pairing with a solenoidal coefficient. -/
theorem coefficientLeray_pairing (k : Frequency) (c v : Fin 3 → ℂ)
    (hsol : (∑ i : Fin 3, (k i : ℂ) * c i) = 0) :
    (∑ i : Fin 3, star (c i) * coefficientLeray k v i) =
      ∑ i : Fin 3, star (c i) * v i := by
  have hstar : (∑ i : Fin 3, star (c i) * (k i : ℂ)) = 0 := by
    simpa only [star_sum, star_mul, star_intCast, star_zero] using congrArg star hsol
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false]
    simp_rw [mul_sub, div_eq_mul_inv, ← mul_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hstar]
    simp

/-- Exact scalar viscous splitting, before any nonlinear cancellation. -/
theorem complex_viscous_pairing (lam : ℝ) (z w : ℂ) :
    (star z * (-(lam : ℂ) * z - w)).re =
      -lam * Complex.normSq z - (star z * w).re := by
  simp [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Fourier coefficient dissipation without the viscosity factor. -/
def coefficientDissipation (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k i)

/-- The projected nonlinear energy-transfer remainder. -/
def coefficientNonlinearPower (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re

/-- Algebraic splitting of the energy rate.  No vanishing remainder is assumed. -/
theorem coefficientEnergy_rate_split (ν : ℝ) (N : ℕ) (c : FourierCoeff) :
    (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      2 * (star (c k i) * galerkinRhs ν N c k i).re) =
      (-2 * ν) * coefficientDissipation N c -
        2 * coefficientNonlinearPower N c := by
  have hpoint (k : Frequency) (i : Fin 3) :
      2 * (star (c k i) * galerkinRhs ν N c k i).re =
        (-2 * ν) *
          ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k i)) -
        2 * (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re := by
    rw [galerkinRhs, complex_viscous_pairing]
    ring
  simp only [hpoint, coefficientDissipation, coefficientNonlinearPower,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Concrete finite energy balance retaining the unresolved nonlinear remainder. -/
theorem GalerkinSolution.coefficientEnergy_balance_with_remainder
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientEnergy N (g.coeff r))
      ((-2 * ν) * coefficientDissipation N (g.coeff t) -
        2 * coefficientNonlinearPower N (g.coeff t)) (Ici 0) t := by
  rw [← coefficientEnergy_rate_split]
  exact g.coefficientEnergy_hasDerivWithinAt ht

end

end SingularClosure
