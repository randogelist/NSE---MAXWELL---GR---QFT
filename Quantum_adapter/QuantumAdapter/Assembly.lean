import QuantumAdapter.Assembly.Flow
import QuantumAdapter.Assembly.CanonicalFlow
import QuantumAdapter.Assembly.CompleteFlow
import QuantumAdapter.Assembly.FlowContinuity
import QuantumAdapter.Assembly.Fourier
import QuantumAdapter.Assembly.Galerkin
import QuantumAdapter.Assembly.Gaussian
import QuantumAdapter.Assembly.Transport
import QuantumAdapter.Assembly.PacketEstimates
import QuantumAdapter.Assembly.Admissibility
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
  calc
    Real.sqrt (energy3 N q) ≤
        Real.sqrt (energy3 N (q - r)) + Real.sqrt (energy3 N r) :=
      sqrt_energy3_le_add N q r
    _ ≤ packetDistance N q r + Real.sqrt (energy3 N r) :=
      add_le_add_right (sqrt_energy3_le_cutoffSobolevFactor_mul_norm N (q - r)) _
    _ = Real.sqrt (energy3 N r) + packetDistance N q r := add_comm _ _

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
    (primitives : PacketEstimatePrimitives F Cemb C3) :
    NSEMaxwell.Classical.FeffermanB ν ↔ QREG F :=
  feffermanB_iff_qreg_of_analytic_bounds F Cemb C3 laws
    (packetBounds_of_scalar_primitives primitives) initialProjectionBounds

theorem exact_quantum_root_with_transport (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (Cemb C3 : ℝ) (laws : GalerkinAnalyticLaws F)
    (primitives : PacketEstimatePrimitives F Cemb C3) :
    PhaseTransportLaws F ∧ (NSEMaxwell.Classical.FeffermanB ν ↔ QREG F) :=
  ⟨phaseTransportLaws_of_jacobian F hd hdet,
    exact_quantum_root_of_scalar_primitives F Cemb C3 laws primitives⟩

/-- Exact remaining frontier after Gaussian, projection and packet integration
have been constructed. The actual PDE and dynamical hypotheses stay visible. -/
theorem exact_quantum_root_of_native_dynamics {C3 : ℝ}
    (hν : 0 < ν) (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t))
    (hC3 : 0 < C3)
    (hrelative : ∀ N (q r : Phase N) t, 0 ≤ t →
      ‖F.map N t q - F.map N t r‖ ≤
        ‖q - r‖ * Real.exp (orbitGradientCost F N r t))
    (htame : ∀ N (q : Phase N) t, 0 ≤ t →
      Real.sqrt (energy3 N (F.map N t q)) ≤
        Real.sqrt (energy3 N q) * Real.exp (C3 * orbitGradientCost F N q t))
    (laws : GalerkinAnalyticLaws F) :
    NSEMaxwell.Classical.FeffermanB ν ↔ QREG F :=
  feffermanB_iff_qreg_of_analytic_bounds F gradientEmbeddingConstant C3 laws
    (packetBounds_of_jacobian hν.le F hd hdet hC3 hrelative htame)
    initialProjectionBounds

end
end QuantumAdapter.Assembly
