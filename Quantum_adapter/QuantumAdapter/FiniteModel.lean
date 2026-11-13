import QuantumAdapter.Phase
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Full finite Fourier observables and a concrete projected vector field

The coefficient convolution contains the zero mode and therefore arbitrary
constant-mean advection. `drift` is explicitly the real orthogonal projection
of that finite Fourier RHS into `Phase N`. Equality to the raw RHS requires
the separate tangency proposition below; no inhabitant is assumed or defined.
Likewise no global flow or continuum solution is supplied by these definitions.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter

noncomputable section

open SingularClosure

def laplaceSymbol (k : Frequency) : ℝ :=
  (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)

theorem laplaceSymbol_nonneg (k : Frequency) : 0 ≤ laplaceSymbol k := by
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  exact mul_nonneg (sq_nonneg _) hk

def h3Weight (k : Frequency) : ℝ := (1 + laplaceSymbol k) ^ 3

theorem h3Weight_pos (k : Frequency) : 0 < h3Weight k := by
  have hk := laplaceSymbol_nonneg k
  unfold h3Weight
  positivity

def energy3 (N : ℕ) (q : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, ∑ i : Fin 3, h3Weight k * Complex.normSq (phaseCoeff q k i)

theorem energy3_nonneg (N : ℕ) (q : Phase N) : 0 ≤ energy3 N q := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (h3Weight_pos k).le (sq_nonneg _)

@[simp]
theorem energy3_zero (N : ℕ) : energy3 N 0 = 0 := by
  simp [energy3]

/-- Actual full Fourier physical synthesis, retaining the constant mode. -/
def synthesis {N : ℕ} (q : Phase N) : Field :=
  fun x => WithLp.toLp 2 (fun i : Fin 3 =>
    (∑ k ∈ fullModes N, fourierCharacter k x * phaseCoeff q k i).re)

def meanVector {N : ℕ} (q : Phase N) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => (phaseCoeff q 0 i).re)

theorem synthesis_eq_mean_add_source {N : ℕ} (q : Phase N) :
    synthesis q = fun x => meanVector q + finiteSynthesis N (phaseCoeff q) x := by
  funext x
  ext i
  simp [synthesis, meanVector, fullModes, finiteSynthesis,
    cutoffModes_zero_not_mem, fourierCharacter]

@[simp]
theorem synthesis_zero (N : ℕ) : synthesis (0 : Phase N) = 0 := by
  funext x
  ext i
  simp [synthesis]

/-- Pointwise squared Frobenius gradient norm. -/
def gradientSquare {N : ℕ} (q : Phase N) (x : Vec) : ℝ :=
  ∑ i : Fin 3, ‖coordinateDerivative (synthesis q) i x‖ ^ 2

/-- The actual spatial gradient supremum; boundedness is a separate theorem. -/
def gradientObservable {N : ℕ} (q : Phase N) : ℝ :=
  sSup (Set.range (fun x : Vec => Real.sqrt (gradientSquare q x)))

def fullTransport (N : ℕ) (c : FourierCoeff) (k : Frequency)
    (i : Fin 3) : ℂ :=
  ∑ p ∈ fullModes N,
    (∑ j : Fin 3,
      c p j * (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) *
      c (k - p) i

theorem fullTransport_eq_source_add_mean (N : ℕ) (c : FourierCoeff)
    (k : Frequency) (i : Fin 3) :
    fullTransport N c k i =
      (∑ j : Fin 3,
        c 0 j * (((2 * Real.pi * (k j : ℝ) : ℝ) : ℂ) * Complex.I)) * c k i +
      coefficientTransport N c k i := by
  simp [fullTransport, fullModes, coefficientTransport, cutoffModes_zero_not_mem]

theorem fullTransport_eq_source_of_mean_zero (N : ℕ) (c : FourierCoeff)
    (hc : ∀ i : Fin 3, c 0 i = 0) (k : Frequency) (i : Fin 3) :
    fullTransport N c k i = coefficientTransport N c k i := by
  rw [fullTransport_eq_source_add_mean]
  simp [hc]

@[simp]
theorem fullTransport_zero (N : ℕ) (k : Frequency) (i : Fin 3) :
    fullTransport N (0 : FourierCoeff) k i = 0 := by
  simp [fullTransport]

@[simp]
theorem fullTransport_zero_fun (N : ℕ) (k : Frequency) :
    fullTransport N (0 : FourierCoeff) k = 0 := by
  funext i
  exact fullTransport_zero N k i

/-- Explicit finite projected-convection coefficient RHS; mean is frozen. -/
def rawRhs (ν : ℝ) (N : ℕ) (q : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki =>
    if ki.1.val = 0 then 0 else
      -((ν * laplaceSymbol ki.1.val : ℝ) : ℂ) * phaseCoeff q ki.1.val ki.2 -
        coefficientLeray ki.1.val (fullTransport N (phaseCoeff q) ki.1.val) ki.2)

theorem rawRhs_mean (ν : ℝ) (N : ℕ) (q : Phase N) (i : Fin 3) :
    extendCoeff (rawRhs ν N q) 0 i = 0 := by
  simp [extendCoeff, rawRhs, zero_mem_fullModes]

@[simp]
theorem rawRhs_zero (ν : ℝ) (N : ℕ) : rawRhs ν N 0 = 0 := by
  ext ki
  by_cases hk : ki.1.val = 0
  · simp [rawRhs, hk]
  · simp [rawRhs, hk, fullTransport_zero_fun, coefficientLeray_zero]

/-- Explicit remaining tangency proposition; this definition is not its proof. -/
def RawRhsTangent : Prop :=
  ∀ ν : ℝ, ∀ N : ℕ, ∀ q : Phase N, rawRhs ν N q ∈ phaseSubmodule N

/-- Concrete orthogonal projection, with no choice of an abstract drift. -/
def drift (ν : ℝ) (N : ℕ) (q : Phase N) : Phase N :=
  (phaseSubmodule N).orthogonalProjectionOnto (rawRhs ν N q)

@[simp]
theorem drift_zero (ν : ℝ) (N : ℕ) : drift ν N 0 = 0 := by
  simp [drift]

theorem drift_eq_rawRhs_of_tangent (h : RawRhsTangent)
    (ν : ℝ) (N : ℕ) (q : Phase N) :
    (drift ν N q).val = rawRhs ν N q := by
  have hm : rawRhs ν N q ∈ phaseSubmodule N := h ν N q
  have hp := (phaseSubmodule N).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨rawRhs ν N q, hm⟩ : Phase N)
  exact congrArg Subtype.val hp

/-- Actual finite ODE trajectory. No existence field is hidden in this predicate. -/
structure IsTrajectory (ν : ℝ) (N : ℕ) (q₀ : Phase N)
    (q : ℝ → Phase N) : Prop where
  continuous : ContinuousOn q (Ici 0)
  initial : q 0 = q₀
  equation : ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt q (drift ν N (q t)) (Ici 0) t

theorem zero_isTrajectory (ν : ℝ) (N : ℕ) :
    IsTrajectory ν N 0 (fun _ => 0) := by
  refine ⟨continuousOn_const, rfl, ?_⟩
  intro t ht
  rw [drift_zero]
  exact (hasDerivAt_const t (0 : Phase N)).hasDerivWithinAt

/-- The genuine cotangent lift of the explicitly defined finite drift. -/
def cotangentHamiltonian (ν : ℝ) (N : ℕ) (q p : Phase N) : ℝ :=
  inner ℝ p (drift ν N q)

theorem cotangent_momentum_increment (ν : ℝ) (N : ℕ)
    (q p r : Phase N) (s : ℝ) :
    cotangentHamiltonian ν N q (p + s • r) =
      cotangentHamiltonian ν N q p + s * cotangentHamiltonian ν N q r := by
  simp [cotangentHamiltonian, inner_add_left, inner_smul_left]

@[simp]
theorem cotangent_zero_momentum (ν : ℝ) (N : ℕ) (q : Phase N) :
    cotangentHamiltonian ν N q 0 = 0 := by
  simp [cotangentHamiltonian]

@[simp]
theorem cotangent_zero_configuration (ν : ℝ) (N : ℕ) (p : Phase N) :
    cotangentHamiltonian ν N 0 p = 0 := by
  simp [cotangentHamiltonian]

end

end QuantumAdapter
