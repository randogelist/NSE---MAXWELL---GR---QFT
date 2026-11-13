import QuantumAdapter.Dynamics
import NSEMaxwell.Classical

/-!
# Exact finite-cutoff regularity contracts

All scalar expressions below are the actual finite Fourier energy or the actual
transported-packet expectation. The native classical endpoint is unchanged.

`PacketBounds` contains quantitative estimates at a single cutoff. It contains
neither `G3`, `QREG`, `FeffermanB`, nor an implication between those propositions.
`GalerkinAnalyticLaws` contains smooth-solution stability and fixed-datum
compactness. No inhabitant of either analytic contract is supplied here.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter

open NSEMaxwell.Classical

noncomputable section

variable {ν : ℝ}

/-- Central actual finite Fourier energy; arbitrary initial means are retained. -/
def centralEnergy (F : PhaseFlow ν) (N : ℕ) (a : Field)
    (ha : Data a) (t : ℝ) : ℝ :=
  energy3 N (F.map N t (initialPhaseData N a ha))

/-- The actual Gaussian-packet energy expectation centered at the projected datum. -/
def packetEnergy (F : PhaseFlow ν) (N : ℕ) (a : Field)
    (ha : Data a) (t : ℝ) : ℝ :=
  quantumEnergy F N (initialPhaseData N a ha) t

/-- One datum and one finite horizon; the bound is independent of the cutoff. -/
def GalerkinBoundAt (F : PhaseFlow ν) (a : Field) (ha : Data a)
    (T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
    0 ≤ t → t ≤ T → centralEnergy F N a ha t ≤ C

/-- All smooth arbitrary-mean data and all positive finite horizons. -/
def G3 (F : PhaseFlow ν) : Prop :=
  ∀ (a : Field) (ha : Data a) (T : ℝ), 0 < T →
    GalerkinBoundAt F a ha T

/-- Actual state/observable admissibility accompanies every expectation bound.
This prevents a nonintegrable totalized integral from witnessing regularity. -/
structure QREG (F : PhaseFlow ν) : Prop where
  admissible : ∀ (a : Field) (ha : Data a) (N : ℕ), 1 ≤ N →
    ∀ t : ℝ, 0 ≤ t → quantumAdmissible F N (initialPhaseData N a ha) t
  bounded : ∀ (a : Field) (ha : Data a) (T : ℝ), 0 < T →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      0 ≤ t → t ≤ T → packetEnergy F N a ha t ≤ C

/-- M11 for canonical Gaussian second-moment radius D₂ = 1/2.
The argument C bounds the square of the central H3 norm. -/
def forwardPacketBound (Cemb T C : ℝ) : ℝ :=
  (Real.sqrt C + (1 / 2 : ℝ) * Real.exp (Cemb * Real.sqrt C * T)) ^ 2

/-- The M12 integrated-gradient majorant obtained from packet energy C. -/
def packetGradientBudget (Cemb T C : ℝ) : ℝ :=
  Cemb * T * Real.sqrt C

/-- M13 with λ = 1 and D₂ = 1/2; no division by the energy bound occurs. -/
def reversePacketBound (Cemb C3 T A C : ℝ) : ℝ :=
  let L := packetGradientBudget Cemb T C
  let S := L + (1 / 4 : ℝ)
  let R := Real.sqrt ((1 / 4 : ℝ) + L)
  ((A + R) * Real.exp (C3 * S) + R * Real.exp S) ^ 2

theorem forwardPacketBound_nonneg (Cemb T C : ℝ) :
    0 ≤ forwardPacketBound Cemb T C := by
  exact sq_nonneg _

theorem reversePacketBound_nonneg (Cemb C3 T A C : ℝ) :
    0 ≤ reversePacketBound Cemb C3 T A C := by
  exact sq_nonneg _

/-- Open actual packet estimates at each cutoff; constants are cutoff-independent.
No global regularity proposition is a field of this structure. -/
structure PacketBounds (F : PhaseFlow ν) (Cemb C3 : ℝ) : Prop where
  embedding_pos : 0 < Cemb
  tame_pos : 0 < C3
  admissible : ∀ (N : ℕ), 1 ≤ N → ∀ (q₀ : Phase N) (t : ℝ), 0 ≤ t →
    quantumAdmissible F N q₀ t
  forward_estimate : ∀ (N : ℕ), 1 ≤ N → ∀ (q₀ : Phase N) (T C : ℝ),
    0 < T → 0 ≤ C →
    (∀ t : ℝ, 0 ≤ t → t ≤ T → energy3 N (F.map N t q₀) ≤ C) →
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      quantumEnergy F N q₀ t ≤ forwardPacketBound Cemb T C
  reverse_estimate : ∀ (N : ℕ), 1 ≤ N → ∀ (q₀ : Phase N) (T A C : ℝ),
    0 < T → 0 ≤ A → 0 ≤ C → energy3 N q₀ ≤ A ^ 2 →
    (∀ t : ℝ, 0 ≤ t → t ≤ T → quantumEnergy F N q₀ t ≤ C) →
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      energy3 N (F.map N t q₀) ≤ reversePacketBound Cemb C3 T A C

/-- Uniform initial Fourier energy bound for each actual smooth datum.
This is an explicit analytic premise until the Sobolev projection adapter passes. -/
def InitialProjectionBounds : Prop :=
  ∀ (a : Field) (ha : Data a), ∃ A : ℝ, 0 ≤ A ∧
    ∀ N : ℕ, 1 ≤ N → energy3 N (initialPhaseData N a ha) ≤ A ^ 2

/-- Open local analytic endpoints for the actual Galerkin flow.
Neither field is a map between the global regularity propositions. -/
structure GalerkinAnalyticLaws (F : PhaseFlow ν) : Prop where
  smooth_stability : ∀ (a : Field) (ha : Data a) (u : Velocity) (p : Pressure),
    NSSolution ν a u p → ∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T
  compactness : ∀ (a : Field) (ha : Data a),
    (∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T) →
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p

/-- The exact native classical endpoint and actual Gaussian energy criterion.
The flow is an explicit argument; existence of a canonical flow is separate. -/
def ExactQuantumEquivalence (F : PhaseFlow ν) : Prop :=
  NSEMaxwell.Classical.FeffermanB ν ↔ QREG F

end

end QuantumAdapter
