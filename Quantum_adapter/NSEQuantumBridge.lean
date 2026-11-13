import NSEQuantumForward
import NSEQuantumReverse

/-!
# Exact conditional Fefferman / quantum regularity assembly

The four unresolved inputs are visible in the theorem types:
the actual `PhaseFlow`, local `GalerkinAnalyticLaws`, quantitative
`PacketBounds`, and `InitialProjectionBounds`.

This theorem does not construct a `PhaseFlow`, prove its raw-drift tangent
identity, construct a selfadjoint Hilbert-space generator, or supply an
inhabitant of any of the analytic contracts. It is the deterministic
composition of the six ordered implications in the two direction modules.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter

open NSEMaxwell.Classical
open Directions

noncomputable section

variable {ν : ℝ}

/-- Exact conjunction of the independently proved forward and reverse edges. -/
theorem feffermanB_iff_qreg_of_analytic_bounds
    (F : PhaseFlow ν) (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (packets : PacketBounds F Cemb C3) (initial : InitialProjectionBounds) :
    NSEMaxwell.Classical.FeffermanB ν ↔ QREG F := by
  exact ⟨feffermanB_implies_quantum_of_analyticLaws F Cemb C3 laws packets,
    quantum_implies_feffermanB_of_analyticLaws F Cemb C3 laws packets initial⟩

/-- Concrete target alias; the native arbitrary-mean classical endpoint remains unchanged. -/
theorem exactQuantumEquivalence_of_analytic_bounds
    (F : PhaseFlow ν) (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (packets : PacketBounds F Cemb C3) (initial : InitialProjectionBounds) :
    ExactQuantumEquivalence F := by
  exact feffermanB_iff_qreg_of_analytic_bounds F Cemb C3 laws packets initial

/-- Positive-viscosity root with the complete explicit semantic and analytic prefix.
The hbar-independent transport observable does not acquire a dummy hbar parameter. -/
theorem exact_quantum_conditional_root :
    ∀ ν : ℝ, 0 < ν → ∀ F : PhaseFlow ν, ∀ Cemb C3 : ℝ,
      GalerkinAnalyticLaws F → PacketBounds F Cemb C3 →
      InitialProjectionBounds →
      (NSEMaxwell.Classical.FeffermanB ν ↔ QREG F) := by
  intro ν _hν F Cemb C3 laws packets initial
  exact feffermanB_iff_qreg_of_analytic_bounds F Cemb C3 laws packets initial

end

end QuantumAdapter
