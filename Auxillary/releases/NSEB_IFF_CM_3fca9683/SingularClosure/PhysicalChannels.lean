import SingularClosure.Galerkin

/-!
# Finite physical synthesis of the six channels

These theorems concern the actual real trigonometric-polynomial fields used by
`GalerkinSolution.velocity`.  They prove reconstruction and derivative
reconstruction, not the physical Parseval or enstrophy identity.  In particular,
the spectral orthogonality theorem is not silently identified with an integral
orthogonality theorem.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem finiteSynthesis_add (N : ℕ) (a b : FourierCoeff) :
    finiteSynthesis N (a + b) = finiteSynthesis N a + finiteSynthesis N b := by
  funext x
  ext i
  simp [finiteSynthesis, mul_add, Finset.sum_add_distrib]

theorem finiteSynthesis_sum {ι : Type*} (N : ℕ) (s : Finset ι)
    (a : ι → FourierCoeff) :
    finiteSynthesis N (∑ i ∈ s, a i) = ∑ i ∈ s, finiteSynthesis N (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, finiteSynthesis_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, finiteSynthesis_add, ih, Finset.sum_insert hi]

/-- A physical channel is the concrete real synthesis of the corresponding mask. -/
def physicalChannel (N : ℕ) (A : Fin 6) (a : FourierCoeff) : Field :=
  finiteSynthesis N (spectralChannel A a)

/-- Exact reconstruction as real fields, at every point of the physical lift. -/
theorem SIX_CHANNEL_FINITE_RECONSTRUCTION (N : ℕ) (a : FourierCoeff) :
    (∑ A : Fin 6, physicalChannel N A a) = finiteSynthesis N a := by
  unfold physicalChannel
  rw [← finiteSynthesis_sum, spectralChannel_sum]

theorem physicalChannel_idempotent (N : ℕ) (A : Fin 6) (a : FourierCoeff) :
    physicalChannel N A (spectralChannel A a) = physicalChannel N A a := by
  unfold physicalChannel
  rw [spectralChannel_idempotent]

theorem physicalChannel_disjoint (N : ℕ) (A B : Fin 6) (hAB : A ≠ B)
    (a : FourierCoeff) : physicalChannel N A (spectralChannel B a) = 0 := by
  unfold physicalChannel
  rw [spectralChannel_disjoint A B hAB, finiteSynthesis_zero]

theorem spectralChannel_v_third_zero (A : Fin 6) (hA : A = 0 ∨ A = 1)
    (a : FourierCoeff) (k : Frequency) : spectralChannel A a k 2 = 0 := by
  rcases hA with rfl | rfl <;>
    by_cases h2 : k 2 = 0 <;>
    by_cases h0 : k 0 = 0 <;>
    simp [spectralChannel, channelOf, h2, h0]

theorem spectralChannel_w_horizontal_zero (A : Fin 6) (hA : A = 2 ∨ A = 3)
    (a : FourierCoeff) (k : Frequency) (i : Fin 3) (hi : i ≠ 2) :
    spectralChannel A a k i = 0 := by
  rcases hA with rfl | rfl <;>
    by_cases h2 : k 2 = 0 <;>
    by_cases h0 : k 0 = 0 <;>
    simp [spectralChannel, channelOf, hi, h2, h0]

/-- The two `v` channels are horizontal physical vectors. -/
theorem physicalChannel_v_third_zero (N : ℕ) (A : Fin 6) (hA : A = 0 ∨ A = 1)
    (a : FourierCoeff) (x : Vec) : physicalChannel N A a x 2 = 0 := by
  change (∑ k ∈ cutoffModes N,
    fourierCharacter k x * spectralChannel A a k 2).re = 0
  simp [spectralChannel_v_third_zero A hA]

/-- The two `w` channels are vertical physical vectors. -/
theorem physicalChannel_w_horizontal_zero (N : ℕ) (A : Fin 6)
    (hA : A = 2 ∨ A = 3) (a : FourierCoeff) (x : Vec) (i : Fin 3)
    (hi : i ≠ 2) : physicalChannel N A a x i = 0 := by
  change (∑ k ∈ cutoffModes N,
    fourierCharacter k x * spectralChannel A a k i).re = 0
  have hz : ∀ k : Frequency, spectralChannel A a k i = 0 :=
    fun k => spectralChannel_w_horizontal_zero A hA a k i hi
  simp [hz]

/-- The horizontal/vertical channel pair is orthogonal even before integration. -/
theorem physicalChannel_v_w_pointwise_orthogonal (N : ℕ) (A B : Fin 6)
    (hA : A = 0 ∨ A = 1) (hB : B = 2 ∨ B = 3) (a b : FourierCoeff)
    (x : Vec) :
    (∑ i : Fin 3, physicalChannel N A a x i * physicalChannel N B b x i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hi2 : i = 2
  · subst i
    rw [physicalChannel_v_third_zero N A hA, zero_mul]
  · rw [physicalChannel_w_horizontal_zero N B hB b x i hi2, mul_zero]

theorem fourierCharacter_contDiff (k : Frequency) :
    ContDiff ℝ ∞ (fourierCharacter k) := by
  have hphase : ContDiff ℝ ∞
      (fun x : Vec => 2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * x i)) := by
    fun_prop
  unfold fourierCharacter
  exact ((Complex.ofRealCLM.contDiff.comp hphase).mul
    (show ContDiff ℝ ∞ (fun _ : Vec => Complex.I) from contDiff_const)).cexp

/-- Finite synthesis is smooth without any summability assumption on the family. -/
theorem finiteSynthesis_contDiff (N : ℕ) (a : FourierCoeff) :
    ContDiff ℝ ∞ (finiteSynthesis N a) := by
  apply (contDiff_piLp 2).2
  intro i
  change ContDiff ℝ ∞
    (fun x : Vec => (∑ k ∈ cutoffModes N, fourierCharacter k x * a k i).re)
  have hsum : ContDiff ℝ ∞
      (fun x : Vec => ∑ k ∈ cutoffModes N, fourierCharacter k x * a k i) :=
    ContDiff.sum fun k _ => (fourierCharacter_contDiff k).mul contDiff_const
  exact Complex.reCLM.contDiff.comp hsum

theorem physicalChannel_contDiff (N : ℕ) (A : Fin 6) (a : FourierCoeff) :
    ContDiff ℝ ∞ (physicalChannel N A a) :=
  finiteSynthesis_contDiff N (spectralChannel A a)

/-- The physical coordinate derivative is linear on this finite smooth synthesis. -/
theorem coordinateDerivative_sum_synthesis {ι : Type*} (N : ℕ) (s : Finset ι)
    (a : ι → FourierCoeff) (j : Fin 3) (x : Vec) :
    coordinateDerivative (∑ i ∈ s, finiteSynthesis N (a i)) j x =
      ∑ i ∈ s, coordinateDerivative (finiteSynthesis N (a i)) j x := by
  unfold coordinateDerivative
  rw [fderiv_sum (fun i _ =>
    (finiteSynthesis_contDiff N (a i)).differentiable (by simp) x)]
  simp

theorem SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION (N : ℕ) (a : FourierCoeff)
    (j : Fin 3) (x : Vec) :
    coordinateDerivative (finiteSynthesis N a) j x =
      ∑ A : Fin 6, coordinateDerivative (physicalChannel N A a) j x := by
  rw [← SIX_CHANNEL_FINITE_RECONSTRUCTION N a]
  exact coordinateDerivative_sum_synthesis N Finset.univ
    (fun A => spectralChannel A a) j x

end

end SingularClosure
