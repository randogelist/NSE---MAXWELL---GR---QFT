import QuantumAdapter.Obligations.TraceSpectrum
import QuantumAdapter.Obligations.TraceViscous

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure QuantumAdapter.Assembly

/-- Exact P1 for the native full real Fourier phase and every real viscosity. -/
theorem native_drift_divergence (ν : ℝ) (N : ℕ) (q : Phase N) :
    driftDivergence ν N q = -phaseDecayRate ν N := by
  rw [driftDivergence_eq_neg_viscosity_mul_trace, phaseLaplacian_trace]
  simp [phaseDecayRate]

end
end QuantumAdapter.Obligations
