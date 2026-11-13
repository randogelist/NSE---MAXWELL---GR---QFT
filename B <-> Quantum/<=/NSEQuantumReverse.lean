import QuantumAdapter.RegularityContracts

/-!
# Ordered reverse implications

The initial projection bound, actual packet estimate, and fixed-datum
compactness theorem are distinct explicit analytic premises.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Directions

open NSEMaxwell.Classical

noncomputable section

variable {ν : ℝ}

/-- R1: M13 with λ=1 converts an actual packet bound to a central bound.
The same A and C are used for every cutoff at the fixed datum and horizon. -/
theorem quantum_implies_galerkin_of_packetBounds
    (F : PhaseFlow ν) (Cemb C3 : ℝ) (packets : PacketBounds F Cemb C3)
    (initial : InitialProjectionBounds) (hQ : QREG F) : G3 F := by
  intro a ha T hT
  obtain ⟨A, hA, hinitial⟩ := initial a ha
  obtain ⟨C, hC, hbound⟩ := hQ.bounded a ha T hT
  refine ⟨reversePacketBound Cemb C3 T A C,
    reversePacketBound_nonneg Cemb C3 T A C, ?_⟩
  intro N hN t ht htT
  exact packets.reverse_estimate N hN (initialPhaseData N a ha) T A C
    hT hA hC (hinitial N hN)
    (fun s hs hsT => hbound N hN s hs hsT) t ht htT

/-- R2: fixed-datum actual compactness supplies the native arbitrary-mean
NSSolution, with the unchanged pressure and t=0 regularity conventions. -/
theorem galerkin_implies_feffermanB_of_analyticLaws
    (F : PhaseFlow ν) (laws : GalerkinAnalyticLaws F)
    (hG : G3 F) : FeffermanB ν := by
  intro a ha
  exact laws.compactness a ha (fun T hT => hG a ha T hT)

/-- R3: deterministic reverse assembly with all unresolved premises named. -/
theorem quantum_implies_feffermanB_of_analyticLaws
    (F : PhaseFlow ν) (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (packets : PacketBounds F Cemb C3) (initial : InitialProjectionBounds)
    (hQ : QREG F) : FeffermanB ν := by
  exact galerkin_implies_feffermanB_of_analyticLaws F laws
    (quantum_implies_galerkin_of_packetBounds F Cemb C3 packets initial hQ)

end

end QuantumAdapter.Directions
