import QuantumAdapter.RegularityContracts

/-!
# Ordered forward implications

The local analytic laws remain explicit. Each theorem has a proved body;
no contract inhabitant or universal regularity bound is constructed here.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Directions

open NSEMaxwell.Classical

noncomputable section

variable {ν : ℝ}

/-- F1: actual smooth solutions imply the central Galerkin criterion,
under the named smooth-solution stability estimate. -/
theorem feffermanB_implies_galerkin_of_analyticLaws
    (F : PhaseFlow ν) (laws : GalerkinAnalyticLaws F)
    (hFB : FeffermanB ν) : G3 F := by
  intro a ha T hT
  obtain ⟨u, p, hsol⟩ := hFB a ha
  exact laws.smooth_stability a ha u p hsol T hT

/-- F2: the explicit M11 bound transports a cutoff-uniform central bound
to actual normalized and integrable quantum states. -/
theorem galerkin_implies_quantum_of_packetBounds
    (F : PhaseFlow ν) (Cemb C3 : ℝ) (packets : PacketBounds F Cemb C3)
    (hG : G3 F) : QREG F := by
  refine ⟨?_, ?_⟩
  · intro a ha N hN t ht
    exact packets.admissible N hN (initialPhaseData N a ha) t ht
  · intro a ha T hT
    obtain ⟨C, hC, hbound⟩ := hG a ha T hT
    refine ⟨forwardPacketBound Cemb T C, forwardPacketBound_nonneg Cemb T C, ?_⟩
    intro N hN t ht htT
    exact packets.forward_estimate N hN (initialPhaseData N a ha) T C hT hC
      (fun s hs hsT => hbound N hN s hs hsT) t ht htT

/-- F3: deterministic assembly; both analytic premises remain in the type. -/
theorem feffermanB_implies_quantum_of_analyticLaws
    (F : PhaseFlow ν) (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (packets : PacketBounds F Cemb C3) (hFB : FeffermanB ν) : QREG F := by
  exact galerkin_implies_quantum_of_packetBounds F Cemb C3 packets
    (feffermanB_implies_galerkin_of_analyticLaws F laws hFB)

end

end QuantumAdapter.Directions
