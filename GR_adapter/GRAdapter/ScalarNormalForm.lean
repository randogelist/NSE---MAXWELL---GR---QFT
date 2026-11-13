import GRAdapter.CompletionSource

/-!
# Exact scalar Hamiltonian normal form

All tensors and contractions are the existing native finite real matrices.
This module proves the algebraic coefficient and solver identities needed
before applying analytic Cauchy--Kowalevski. It does not assert an analytic
existence theorem or an inhabitant of ScalarBoundaryCompletionLaws.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace NSEGR
noncomputable section

/-- The signed Hamiltonian polynomial before trace reversal. -/
def sourceHamiltonian4 (B : Tensor4) : ℝ :=
  lorentzSquare4 B - (lorentzTrace4 B) ^ 2 / 3

def vectorDot3 (u b : Fin 3 → ℝ) : ℝ :=
  u 0 * b 0 + u 1 * b 1 + u 2 * b 2

def frobeniusInner3 (A Q : Tensor3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, A i j * Q i j

/-- The concrete upper-index correction for the scalar jet `(Q,b,s)`. -/
def scalarJetCorrection (Q : Tensor3) (b : Fin 3 → ℝ) (s : ℝ) : Tensor4 :=
  boundaryBlock (trace3 Q) (fun i => -b i)
    (fun i j => Q i j + (s - trace3 Q) * identity3 i j)

def scalarCompletedUpper (ρ : ℝ) (u : Fin 3 → ℝ) (A Q : Tensor3)
    (b : Fin 3 → ℝ) (s : ℝ) : Tensor4 :=
  boundaryBlock ρ u A + scalarJetCorrection Q b s

/-- The exact solved RHS; its nonzero denominator is a theorem hypothesis below. -/
def scalarJetRHS (ρ : ℝ) (u : Fin 3 → ℝ) (A Q : Tensor3)
    (b : Fin 3 → ℝ) : ℝ :=
  (-sourceHamiltonian4 (boundaryBlock ρ u A) - 4 * vectorDot3 u b -
    2 * frobeniusInner3 A Q + 2 * vectorSq3 b - frobeniusSq3 Q + (trace3 Q) ^ 2) /
    (2 * (ρ + trace3 Q))

theorem lorentzTrace4_lowerTensor4 (B : Tensor4) :
    lorentzTrace4 (lowerTensor4 B) = lorentzTrace4 B := by
  simp [lorentzTrace4, lowerTensor4, lorentzSign4]

theorem lorentzSquare4_lowerTensor4 (B : Tensor4) :
    lorentzSquare4 (lowerTensor4 B) = lorentzSquare4 B := by
  simp [lorentzSquare4, lowerTensor4, lorentzSign4, Fin.sum_univ_succ] <;> ring

theorem sourceHamiltonian4_lowerTensor4 (B : Tensor4) :
    sourceHamiltonian4 (lowerTensor4 B) = sourceHamiltonian4 B := by
  simp only [sourceHamiltonian4, lorentzSquare4_lowerTensor4, lorentzTrace4_lowerTensor4]

theorem sourceHamiltonian4_boundaryBlock (ρ : ℝ) (u : Fin 3 → ℝ) (A : Tensor3) :
    sourceHamiltonian4 (boundaryBlock ρ u A) =
      ρ ^ 2 - 2 * vectorSq3 u + frobeniusSq3 A - (-ρ + trace3 A) ^ 2 / 3 := by
  rw [sourceHamiltonian4, lorentzSquare4_boundaryBlock, lorentzTrace4_boundaryBlock]

theorem vectorSq3_sub (u b : Fin 3 → ℝ) :
    vectorSq3 (fun i => u i - b i) =
      vectorSq3 u - 2 * vectorDot3 u b + vectorSq3 b := by
  simp only [vectorSq3, vectorDot3]
  ring

theorem trace3_scalarSpatialJet (A Q : Tensor3) (s : ℝ) :
    trace3 (fun i j => A i j + Q i j + (s - trace3 Q) * identity3 i j) =
      trace3 A + trace3 Q + 3 * (s - trace3 Q) := by
  simp [trace3, identity3] <;> ring

theorem frobeniusSq3_scalarSpatialJet (A Q : Tensor3) (s : ℝ) :
    frobeniusSq3 (fun i j => A i j + Q i j + (s - trace3 Q) * identity3 i j) =
      frobeniusSq3 A + 2 * frobeniusInner3 A Q + frobeniusSq3 Q +
        2 * (s - trace3 Q) * (trace3 A + trace3 Q) + 3 * (s - trace3 Q) ^ 2 := by
  simp [frobeniusSq3, frobeniusInner3, trace3, identity3, Fin.sum_univ_succ] <;> ring

theorem scalarCompletedUpper_eq_block (ρ : ℝ) (u : Fin 3 → ℝ)
    (A Q : Tensor3) (b : Fin 3 → ℝ) (s : ℝ) :
    scalarCompletedUpper ρ u A Q b s =
      boundaryBlock (ρ + trace3 Q) (fun i => u i - b i)
        (fun i j => A i j + Q i j + (s - trace3 Q) * identity3 i j) := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) c
    · rfl
    · change u j + -b j = u j - b j
      ring
  · refine Fin.cases ?_ (fun j => ?_) c
    · change u i + -b i = u i - b i
      ring
    · change A i j + (Q i j + (s - trace3 Q) * identity3 i j) =
        A i j + Q i j + (s - trace3 Q) * identity3 i j
      ring

/-- Exact scalar normal form, for arbitrary finite spatial matrices A and Q.
No symmetry or PDE hypothesis is needed for this entry-square identity. -/
theorem scalar_hamiltonian_expansion (ρ : ℝ) (u : Fin 3 → ℝ)
    (A Q : Tensor3) (b : Fin 3 → ℝ) (s : ℝ) :
    sourceHamiltonian4 (scalarCompletedUpper ρ u A Q b s) =
      sourceHamiltonian4 (boundaryBlock ρ u A) + 2 * (ρ + trace3 Q) * s +
        4 * vectorDot3 u b + 2 * frobeniusInner3 A Q -
        2 * vectorSq3 b + frobeniusSq3 Q - (trace3 Q) ^ 2 := by
  let M : Tensor3 := fun i j => A i j + Q i j + (s - trace3 Q) * identity3 i j
  have htrM : trace3 M = trace3 A + trace3 Q + 3 * (s - trace3 Q) :=
    trace3_scalarSpatialJet A Q s
  have hsqM : frobeniusSq3 M =
      frobeniusSq3 A + 2 * frobeniusInner3 A Q + frobeniusSq3 Q +
        2 * (s - trace3 Q) * (trace3 A + trace3 Q) + 3 * (s - trace3 Q) ^ 2 :=
    frobeniusSq3_scalarSpatialJet A Q s
  calc
    sourceHamiltonian4 (scalarCompletedUpper ρ u A Q b s) =
        sourceHamiltonian4 (boundaryBlock (ρ + trace3 Q) (fun i => u i - b i) M) :=
      congrArg sourceHamiltonian4 (scalarCompletedUpper_eq_block ρ u A Q b s)
    _ = (ρ + trace3 Q) ^ 2 - 2 * vectorSq3 (fun i => u i - b i) + frobeniusSq3 M -
        (-(ρ + trace3 Q) + trace3 M) ^ 2 / 3 :=
      sourceHamiltonian4_boundaryBlock (ρ + trace3 Q) (fun i => u i - b i) M
    _ = sourceHamiltonian4 (boundaryBlock ρ u A) + 2 * (ρ + trace3 Q) * s +
        4 * vectorDot3 u b + 2 * frobeniusInner3 A Q -
        2 * vectorSq3 b + frobeniusSq3 Q - (trace3 Q) ^ 2 := by
      rw [htrM, hsqM, vectorSq3_sub, sourceHamiltonian4_boundaryBlock]
      ring

/-- The expansion remains exact after the native lowering of both indices. -/
theorem scalar_hamiltonian_expansion_lowered (ρ : ℝ) (u : Fin 3 → ℝ)
    (A Q : Tensor3) (b : Fin 3 → ℝ) (s : ℝ) :
    sourceHamiltonian4 (lowerTensor4 (scalarCompletedUpper ρ u A Q b s)) =
      sourceHamiltonian4 (boundaryBlock ρ u A) + 2 * (ρ + trace3 Q) * s +
        4 * vectorDot3 u b + 2 * frobeniusInner3 A Q -
        2 * vectorSq3 b + frobeniusSq3 Q - (trace3 Q) ^ 2 := by
  rw [sourceHamiltonian4_lowerTensor4]
  exact scalar_hamiltonian_expansion ρ u A Q b s

/-- Solving the actual Hamiltonian equation requires exactly this denominator condition. -/
theorem scalar_hamiltonian_zero_iff (ρ : ℝ) (u : Fin 3 → ℝ)
    (A Q : Tensor3) (b : Fin 3 → ℝ) (s : ℝ) (hρQ : ρ + trace3 Q ≠ 0) :
    sourceHamiltonian4 (scalarCompletedUpper ρ u A Q b s) = 0 ↔
      s = scalarJetRHS ρ u A Q b := by
  rw [scalar_hamiltonian_expansion]
  unfold scalarJetRHS
  have hden : 2 * (ρ + trace3 Q) ≠ 0 := mul_ne_zero (by norm_num) hρQ
  rw [eq_div_iff hden]
  constructor <;> intro h <;> nlinarith [h]

theorem scalarJetRHS_solves_hamiltonian (ρ : ℝ) (u : Fin 3 → ℝ)
    (A Q : Tensor3) (b : Fin 3 → ℝ) (hρQ : ρ + trace3 Q ≠ 0) :
    sourceHamiltonian4
      (scalarCompletedUpper ρ u A Q b (scalarJetRHS ρ u A Q b)) = 0 := by
  exact (scalar_hamiltonian_zero_iff ρ u A Q b (scalarJetRHS ρ u A Q b) hρQ).2 rfl

/-- The exact pure-time second-jet coefficient, expressed without a differentiation axiom. -/
theorem scalar_hamiltonian_secondJet_difference (ρ : ℝ) (u : Fin 3 → ℝ)
    (A Q : Tensor3) (b : Fin 3 → ℝ) (s r : ℝ) :
    sourceHamiltonian4 (scalarCompletedUpper ρ u A Q b s) -
      sourceHamiltonian4 (scalarCompletedUpper ρ u A Q b r) =
        2 * (ρ + trace3 Q) * (s - r) := by
  simp only [scalar_hamiltonian_expansion]
  ring

theorem scalar_hamiltonian_initial_jet (ρ : ℝ) (u : Fin 3 → ℝ)
    (A : Tensor3) (s : ℝ) :
    sourceHamiltonian4 (scalarCompletedUpper ρ u A 0 0 s) =
      sourceHamiltonian4 (boundaryBlock ρ u A) + 2 * ρ * s := by
  rw [scalar_hamiltonian_expansion]
  simp [trace3, vectorDot3, frobeniusInner3, vectorSq3, frobeniusSq3] <;> ring

theorem scalar_hamiltonian_initial_noncharacteristic (ρ : ℝ) (hρ : ρ ≠ 0) :
    2 * (ρ + trace3 (0 : Tensor3)) ≠ 0 := by
  simpa only [trace3_zero, add_zero] using
    mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) hρ

/-- This trace identity is definitional finite calculus: no mixed-partial exchange is used. -/
theorem trace3_scalarHessian (f : ScalarField) (x : Vec) :
    trace3 (scalarHessian f x) = scalarLaplacian f x := by
  simp [trace3, scalarHessian, scalarLaplacian, Fin.sum_univ_succ] <;> ring

/-- Exact identification of the concrete derivative-based scalar correction with its finite jet. -/
theorem scalarCompletionUpper_eq_scalarJet (ψ : Pressure) (t : ℝ) (x : Vec) :
    scalarCompletionUpper ψ t x =
      scalarJetCorrection (scalarHessian (ψ t) x)
        (fun i => gradient (scalarLocalTimeDerivative ψ t) x i)
        (scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x) := by
  simp only [scalarCompletionUpper, scalarJetCorrection, trace3_scalarHessian]

/-- The actual spatial block of the native NSE source. -/
def nseSpatialSource3 (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) (x : Vec) : Tensor3 :=
  fun i j => u t x i * u t x j + p t x * identity3 i j - ν * strain (u t) x i j

/-- The derivative-based completed-boundary Hamiltonian equals the finite scalar-jet polynomial. -/
theorem completedBoundary_hamiltonian_eq_scalarJet
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec) :
    boundaryHamiltonian (completedBoundary ν ρ u p ψ) t x =
      sourceHamiltonian4 (scalarCompletedUpper ρ (fun i => u t x i)
        (nseSpatialSource3 ν u p t x) (scalarHessian (ψ t) x)
        (fun i => gradient (scalarLocalTimeDerivative ψ t) x i)
        (scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x)) := by
  rw [completedBoundary_hamiltonian_identity]
  change sourceHamiltonian4 (lowerTensor4
    (conservedSourceUpper ν ρ u p t x + scalarCompletionUpper ψ t x)) = _
  rw [sourceHamiltonian4_lowerTensor4, scalarCompletionUpper_eq_scalarJet]
  rfl

/-- Exact scalar PDE normal form for the actual native derivatives.
Analyticity and existence of a solution of this equation are separate obligations. -/
theorem completedBoundary_hamiltonian_zero_iff_scalar_normal
    (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) (t : ℝ) (x : Vec)
    (hρψ : ρ + scalarLaplacian (ψ t) x ≠ 0) :
    boundaryHamiltonian (completedBoundary ν ρ u p ψ) t x = 0 ↔
      scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x =
        scalarJetRHS ρ (fun i => u t x i) (nseSpatialSource3 ν u p t x)
          (scalarHessian (ψ t) x)
          (fun i => gradient (scalarLocalTimeDerivative ψ t) x i) := by
  rw [completedBoundary_hamiltonian_eq_scalarJet]
  apply scalar_hamiltonian_zero_iff
  simpa only [trace3_scalarHessian] using hρψ

end
end NSEGR
