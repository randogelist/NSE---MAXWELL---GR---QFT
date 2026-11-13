import QuantumAdapter.Assembly.Flow
import QuantumAdapter.Assembly.Fourier
import QuantumAdapter.Assembly.Galerkin
import QuantumAdapter.Assembly.Gaussian
import QuantumAdapter.Assembly.Transport
import QuantumAdapter.Assembly.PacketEstimates
import NSEQuantumBridge

/-!
Native assembly above the pinned Mathlib identities.
The exact root is preserved; undischarged PDE/trajectory hypotheses remain
visible. Compilation and an axiom audit do not construct their inhabitants.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Assembly

noncomputable section

variable {ν : ℝ}

theorem native_initial_packet_triangle (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N q) ≤ Real.sqrt (energy3 N r) + packetDistance N q r := by
  exact (sqrt_energy3_le_add N q r).trans
    (add_le_add_left (sqrt_energy3_le_cutoffSobolevFactor_mul_norm N (q - r)) _)

theorem transportedPacket_waveAdmissible_of_jacobian (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (N : ℕ) (q₀ : Phase N) (t : ℝ) :
    WaveAdmissible (phaseVolume N) (transportedPacket F N q₀ t) :=
  transport_waveAdmissible F (phaseTransportLaws_of_jacobian F hd hdet) N t
    (canonicalPacket_waveAdmissible N q₀)

theorem exact_quantum_root_of_scalar_primitives (F : PhaseFlow ν)
    (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (primitives : PacketEstimatePrimitives F Cemb C3)
    (initial : InitialProjectionBounds) :
    NSEMaxwell.Classical.FeffermanB ν ↔ QREG F :=
  feffermanB_iff_qreg_of_analytic_bounds F Cemb C3 laws
    (packetBounds_of_scalar_primitives primitives) initial

theorem exact_quantum_root_with_transport (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (primitives : PacketEstimatePrimitives F Cemb C3)
    (initial : InitialProjectionBounds) :
    PhaseTransportLaws F ∧ (NSEMaxwell.Classical.FeffermanB ν ↔ QREG F) :=
  ⟨phaseTransportLaws_of_jacobian F hd hdet,
    exact_quantum_root_of_scalar_primitives F Cemb C3 laws primitives initial⟩

end
end QuantumAdapter.Assembly
