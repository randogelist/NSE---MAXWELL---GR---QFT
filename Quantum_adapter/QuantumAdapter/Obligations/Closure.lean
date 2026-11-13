import QuantumAdapter.Assembly
import QuantumAdapter.Obligations.TraceSpectral
import QuantumAdapter.Obligations.VariationalNative
import QuantumAdapter.Obligations.JacobianNative
import QuantumAdapter.Obligations.EnergyRelative
import QuantumAdapter.Obligations.EnergyTame
import QuantumAdapter.Obligations.GalerkinForward
import QuantumAdapter.Obligations.GalerkinReverse

/-!
Deterministic assembly of P1--P7 for the original native quantum equivalence.
The root conclusion is an equivalence. It does not assert either side separately.
This source is a candidate until the matching external build and axiom audit pass.
-/
set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Obligations
noncomputable section
open QuantumAdapter.Assembly

def closedPhaseFlow {ν : ℝ} (hν : 0 < ν) : PhaseFlow ν :=
  canonicalPhaseFlow hν.le (fun N q => native_drift_divergence ν N q)

theorem native_GalerkinAnalyticLaws {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν) :
    GalerkinAnalyticLaws F :=
  ⟨phaseFlow_smooth_stability hν F,phaseFlow_compactness hν F⟩

theorem closedPhaseFlow_transportLaws {ν : ℝ} (hν : 0 < ν) :
    PhaseTransportLaws (closedPhaseFlow hν) :=
  phaseTransportLaws_of_jacobian (closedPhaseFlow hν)
    (phaseFlow_timeMap_differentiable hν.le (closedPhaseFlow hν))
    (phaseFlow_jacobian hν.le (closedPhaseFlow hν))

/-- The exact original equivalence, with the seven analytic obligations constructed. -/
theorem NSE_B_IFF_CANONICAL_QUANTUM {ν : ℝ} (hν : 0 < ν) :
    NSEMaxwell.Classical.FeffermanB ν ↔ QREG (closedPhaseFlow hν) :=
  exact_quantum_root_of_native_dynamics (C3 := 512) hν (closedPhaseFlow hν)
    (phaseFlow_timeMap_differentiable hν.le (closedPhaseFlow hν))
    (phaseFlow_jacobian hν.le (closedPhaseFlow hν)) (by norm_num)
    (phaseFlow_relative_l2 hν.le (closedPhaseFlow hν))
    (phaseFlow_h3_tame hν.le (closedPhaseFlow hν))
    (native_GalerkinAnalyticLaws hν (closedPhaseFlow hν))

end
end QuantumAdapter.Obligations
