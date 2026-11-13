import Mathlib

/-!
# Concrete six-channel Fourier projections

The fixed ordered axes are j = 2 (the third coordinate) and i = 0
(the first coordinate). The channel order is v0, v1, w0, w1, r0, r1.

All statements in this file concern actual complex Fourier coefficient
functions. The passage between these coefficient functions and physical
periodic fields is a separate endpoint; it is not postulated here.

No local Lean execution. Candidate source for external CI verification.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

noncomputable section

namespace SingularClosure

abbrev Frequency := Fin 3 → ℤ
abbrev FourierCoeff := Frequency → Fin 3 → ℂ

/-- The unique channel containing a frequency/component pair. -/
def channelOf (k : Frequency) (c : Fin 3) : Fin 6 :=
  if k 2 = 0 then
    if c = 2 then
      if k 0 = 0 then 2 else 3
    else
      if k 0 = 0 then 0 else 1
  else
    if k 0 = 0 then 4 else 5

/-- The six concrete diagonal Fourier projections. -/
def spectralChannel (A : Fin 6) (a : FourierCoeff) : FourierCoeff :=
  fun k c => if channelOf k c = A then a k c else 0

def SpectralMeanZero (a : FourierCoeff) : Prop :=
  ∀ c, a 0 c = 0

def SpectralSolenoidal (a : FourierCoeff) : Prop :=
  ∀ k, ∑ c : Fin 3, (k c : ℂ) * a k c = 0

def SpectralReality (a : FourierCoeff) : Prop :=
  ∀ k c, a (-k) c = star (a k c)

/-- Scalar Fourier multipliers include derivatives, heat flow and cutoffs. -/
def spectralMultiplier (m : Frequency → ℂ) (a : FourierCoeff) : FourierCoeff :=
  fun k c => m k * a k c

theorem spectralChannel_sum_apply (a : FourierCoeff) (k : Frequency) (c : Fin 3) :
    ∑ A : Fin 6, spectralChannel A a k c = a k c := by
  classical
  simp [spectralChannel, eq_comm]

theorem spectralChannel_sum (a : FourierCoeff) :
    ∑ A : Fin 6, spectralChannel A a = a := by
  classical
  funext k c
  simpa only [Finset.sum_apply] using spectralChannel_sum_apply a k c

theorem spectralChannel_idempotent (A : Fin 6) (a : FourierCoeff) :
    spectralChannel A (spectralChannel A a) = spectralChannel A a := by
  funext k c
  by_cases h : channelOf k c = A <;> simp [spectralChannel, h]

theorem spectralChannel_disjoint (A B : Fin 6) (hAB : A ≠ B)
    (a : FourierCoeff) :
    spectralChannel A (spectralChannel B a) = 0 := by
  funext k c
  by_cases hA : channelOf k c = A
  · have hB : channelOf k c ≠ B := fun h => hAB (hA.symm.trans h)
    simp [spectralChannel, hB]
  · simp [spectralChannel, hA]

theorem spectralChannel_add (A : Fin 6) (a b : FourierCoeff) :
    spectralChannel A (a + b) = spectralChannel A a + spectralChannel A b := by
  funext k c
  by_cases h : channelOf k c = A <;> simp [spectralChannel, h]

theorem spectralChannel_smul (A : Fin 6) (z : ℂ) (a : FourierCoeff) :
    spectralChannel A (z • a) = z • spectralChannel A a := by
  funext k c
  by_cases h : channelOf k c = A <;> simp [spectralChannel, h]

theorem spectralChannel_commutes_multiplier (A : Fin 6)
    (m : Frequency → ℂ) (a : FourierCoeff) :
    spectralChannel A (spectralMultiplier m a) =
      spectralMultiplier m (spectralChannel A a) := by
  funext k c
  by_cases h : channelOf k c = A <;> simp [spectralChannel, spectralMultiplier, h]

theorem spectralChannel_selfAdjoint_component (A : Fin 6)
    (a b : FourierCoeff) (k : Frequency) (c : Fin 3) :
    star (spectralChannel A a k c) * b k c =
      star (a k c) * spectralChannel A b k c := by
  by_cases h : channelOf k c = A <;> simp [spectralChannel, h]

theorem spectralChannel_selfAdjoint_frequency (A : Fin 6)
    (a b : FourierCoeff) (k : Frequency) :
    (∑ c : Fin 3, star (spectralChannel A a k c) * b k c) =
      ∑ c : Fin 3, star (a k c) * spectralChannel A b k c := by
  apply Finset.sum_congr rfl
  intro c _
  exact spectralChannel_selfAdjoint_component A a b k c

theorem spectralChannel_orthogonal_component (A B : Fin 6) (hAB : A ≠ B)
    (a b : FourierCoeff) (k : Frequency) (c : Fin 3) :
    star (spectralChannel A a k c) * spectralChannel B b k c = 0 := by
  by_cases hA : channelOf k c = A
  · have hB : channelOf k c ≠ B := fun h => hAB (hA.symm.trans h)
    simp [spectralChannel, hB]
  · simp [spectralChannel, hA]

theorem spectralChannel_orthogonal_frequency (A B : Fin 6) (hAB : A ≠ B)
    (a b : FourierCoeff) (k : Frequency) :
    (∑ c : Fin 3, star (spectralChannel A a k c) * spectralChannel B b k c) = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  exact spectralChannel_orthogonal_component A B hAB a b k c

theorem spectralChannel_preserves_meanZero (A : Fin 6)
    {a : FourierCoeff} (ha : SpectralMeanZero a) :
    SpectralMeanZero (spectralChannel A a) := by
  intro c
  simp [spectralChannel, ha c]

theorem channelOf_neg (k : Frequency) (c : Fin 3) :
    channelOf (-k) c = channelOf k c := by
  simp [channelOf]

theorem spectralChannel_preserves_reality (A : Fin 6)
    {a : FourierCoeff} (ha : SpectralReality a) :
    SpectralReality (spectralChannel A a) := by
  intro k c
  by_cases h : channelOf k c = A
  · simp [spectralChannel, channelOf_neg, h, ha k c]
  · simp [spectralChannel, channelOf_neg, h]

theorem spectralChannel_preserves_solenoidal (A : Fin 6)
    {a : FourierCoeff} (ha : SpectralSolenoidal a) :
    SpectralSolenoidal (spectralChannel A a) := by
  intro k
  have hsol := ha k
  fin_cases A <;>
    by_cases h0 : k 0 = 0 <;>
    by_cases h2 : k 2 = 0 <;>
    simp_all [spectralChannel, channelOf, Fin.sum_univ_succ]

/-- A concrete reconstruction/idempotence/disjointness certificate. -/
theorem SIX_CHANNEL_SPECTRAL_PROJECTIONS :
    (∀ a : FourierCoeff, (∑ A : Fin 6, spectralChannel A a) = a) ∧
    (∀ (A : Fin 6) (a : FourierCoeff),
      spectralChannel A (spectralChannel A a) = spectralChannel A a) ∧
    (∀ (A B : Fin 6), A ≠ B → ∀ a : FourierCoeff,
      spectralChannel A (spectralChannel B a) = 0) := by
  exact ⟨spectralChannel_sum, spectralChannel_idempotent, spectralChannel_disjoint⟩

end SingularClosure
