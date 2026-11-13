import QuantumAdapter.FiniteModel
import QuantumAdapter.Transport
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Concrete phase-space quantum expressions

Intrinsic real Hilbert phase volume is used, never the restriction of ambient
complex Lebesgue measure to a proper real subspace. The Gaussian and transport
are actual functions. `PhaseFlow` retains the actual finite ODE and divergence
identity as explicit obligations; this file does not supply a global flow.
The first-order Hamiltonian expression is not asserted selfadjoint.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter

noncomputable section

instance phaseMeasurableSpace (N : ℕ) : MeasurableSpace (Phase N) :=
  borel (Phase N)

instance phaseBorelSpace (N : ℕ) : BorelSpace (Phase N) := ⟨rfl⟩

def phaseDimension (N : ℕ) : ℕ := Module.finrank ℝ (Phase N)

/-- Intrinsic Lebesgue measure of the real constrained Hilbert phase. -/
def phaseVolume (N : ℕ) : Measure (Phase N) :=
  (stdOrthonormalBasis ℝ (Phase N)).toBasis.addHaar

abbrev QuantumHilbert (N : ℕ) := Lp ℂ 2 (phaseVolume N)

def cutoffSobolevFactor (N : ℕ) : ℝ :=
  Real.sqrt ((1 + 4 * Real.pi ^ 2 * (N : ℝ) ^ 2) ^ 3)

theorem cutoffSobolevFactor_pos (N : ℕ) : 0 < cutoffSobolevFactor N := by
  unfold cutoffSobolevFactor
  positivity

/-- Exact canonical Gaussian standard deviation from the B-tier derivation. -/
def canonicalScale (N : ℕ) : ℝ :=
  ((N + 1 : ℝ) * cutoffSobolevFactor N * Real.sqrt (phaseDimension N : ℝ))⁻¹

theorem canonicalScale_pos (N : ℕ) : 0 < canonicalScale N := by
  have hd : (0 : ℝ) < (phaseDimension N : ℝ) := by
    exact_mod_cast phase_finrank_pos N
  have hw := cutoffSobolevFactor_pos N
  unfold canonicalScale
  positivity

def gaussianAmplitude (N : ℕ) : ℝ :=
  Real.rpow (2 * Real.pi * canonicalScale N ^ 2) (-(phaseDimension N : ℝ) / 4)

def canonicalPacket (N : ℕ) (q₀ : Phase N) : Wave (Phase N) :=
  fun q => ((gaussianAmplitude N *
    Real.exp (-‖q - q₀‖ ^ 2 / (4 * canonicalScale N ^ 2)) : ℝ) : ℂ)

theorem canonicalPacket_im (N : ℕ) (q₀ q : Phase N) :
    (canonicalPacket N q₀ q).im = 0 := by
  simp [canonicalPacket]

theorem canonicalPacket_center (N : ℕ) (q₀ : Phase N) :
    canonicalPacket N q₀ q₀ = (gaussianAmplitude N : ℂ) := by
  simp [canonicalPacket]

/-- Full divergence-free Laplace trace, including zero contribution from means. -/
def finiteLaplaceTrace (N : ℕ) : ℝ :=
  ∑ k ∈ fullModes N, 2 * laplaceSymbol k

theorem finiteLaplaceTrace_nonneg (N : ℕ) : 0 ≤ finiteLaplaceTrace N := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (by norm_num) (laplaceSymbol_nonneg k)

def phaseDecayRate (ν : ℝ) (N : ℕ) : ℝ := ν * finiteLaplaceTrace N

def driftDivergence (ν : ℝ) (N : ℕ) (q : Phase N) : ℝ :=
  ∑ i : Fin (phaseDimension N),
    inner ℝ (stdOrthonormalBasis ℝ (Phase N) i)
      (fderiv ℝ (drift ν N) q (stdOrthonormalBasis ℝ (Phase N) i))

/-- A specified complete flow of the actual finite vector field.
Every field is an explicit analytic premise; no inhabitant is supplied here. -/
structure PhaseFlow (ν : ℝ) where
  map : ∀ N : ℕ, ℝ → Phase N → Phase N
  map_zero : ∀ N q, map N 0 q = q
  map_add : ∀ N t s q, map N (t + s) q = map N t (map N s q)
  orbit_derivative : ∀ N q t,
    HasDerivAt (fun s => map N s q) (drift ν N (map N t q)) t
  divergence_eq : ∀ N q, driftDivergence ν N q = -phaseDecayRate ν N

def transport {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (t : ℝ)
    (ψ : Wave (Phase N)) : Wave (Phase N) :=
  halfDensityPullback (phaseDecayRate ν N) (F.map N) t ψ

def transportedPacket {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) (t : ℝ) : Wave (Phase N) :=
  transport F N t (canonicalPacket N q₀)

def quantumEnergy {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) (t : ℝ) : ℝ :=
  expectation (phaseVolume N) (energy3 N) (transportedPacket F N q₀ t)

/-- Full L2 multiplier domain and actual integrable expectation are retained. -/
def quantumAdmissible {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) (t : ℝ) : Prop :=
  WaveAdmissible (phaseVolume N) (transportedPacket F N q₀ t) ∧
  MultiplierDomain (phaseVolume N) (energy3 N) (transportedPacket F N q₀ t) ∧
  ObservableIntegrable (phaseVolume N) (energy3 N) (transportedPacket F N q₀ t)

theorem quantumEnergy_nonneg {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) (t : ℝ) : 0 ≤ quantumEnergy F N q₀ t :=
  expectation_nonneg (phaseVolume N) (energy3 N) _ (energy3_nonneg N)

theorem transport_zero {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (ψ : Wave (Phase N)) : transport F N 0 ψ = ψ := by
  funext q
  simp [transport, halfDensityPullback, F.map_zero]

theorem transportedPacket_zero {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) : transportedPacket F N q₀ 0 = canonicalPacket N q₀ :=
  transport_zero F N _

theorem phaseFlow_isTrajectory {ν : ℝ} (F : PhaseFlow ν) (N : ℕ)
    (q₀ : Phase N) : IsTrajectory ν N q₀ (fun t => F.map N t q₀) := by
  refine ⟨?_, F.map_zero N q₀, ?_⟩
  · exact (continuous_iff_continuousAt.mpr
      (fun t => (F.orbit_derivative N q₀ t).continuousAt)).continuousOn
  · intro t ht
    exact (F.orbit_derivative N q₀ t).hasDerivWithinAt

/-- Actual first-order differential expression on complex test functions. -/
def hamiltonianExpression (ν ℏ : ℝ) (N : ℕ)
    (ψ : Wave (Phase N)) : Wave (Phase N) :=
  fun q => -(Complex.I * (ℏ : ℂ)) *
    (fderiv ℝ ψ q (drift ν N q) + ((driftDivergence ν N q / 2 : ℝ) : ℂ) * ψ q)

theorem hamiltonianExpression_zero (ν ℏ : ℝ) (N : ℕ) :
    hamiltonianExpression ν ℏ N (fun _ => 0) = 0 := by
  funext q
  simp [hamiltonianExpression]

/-- Actual measure-transport obligations, separated from algebraic flow laws. -/
structure PhaseTransportLaws {ν : ℝ} (F : PhaseFlow ν) : Prop where
  integral_law : ∀ N,
    IntegralPullbackLaw (phaseVolume N) (phaseDecayRate ν N) (F.map N)
  memLp_law : ∀ N,
    MemLpPullbackLaw (phaseVolume N) (phaseDecayRate ν N) (F.map N)

end

end QuantumAdapter
