import QuantumAdapter.Obligations.Jacobian
import QuantumAdapter.Obligations.VariationalNative

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Obligations

noncomputable section

/-- P3 for the actual native finite flow, with its variational equation derived. -/
theorem phaseFlow_jacobian {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (t : ℝ) (q : Phase N) :
    (fderiv ℝ (F.map N t) q).det = Real.exp (-(phaseDecayRate ν N) * t) :=
  phaseFlow_jacobian_of_fderiv_variational F
    (fun N q t => phaseFlow_fderiv_hasDerivAt hν F N q t) N t q

end
end QuantumAdapter.Obligations
