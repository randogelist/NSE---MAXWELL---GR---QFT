import QuantumAdapter.Obligations.TraceNonlinear
import QuantumAdapter.Obligations.TraceLaplacian

/-!
Exact affine-viscosity trace decomposition. The remaining spectral task is
the trace of the positive Laplacian on the constrained real phase.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure QuantumAdapter.Assembly

theorem driftDivergence_eq_neg_viscosity_mul_trace (ν : ℝ) (N : ℕ) (q : Phase N) :
    driftDivergence ν N q =
      -ν * LinearMap.trace ℝ (Phase N) (phaseLaplacian N) := by
  rw [driftDivergence_eq_linearTrace, drift_fderiv_viscosity_split]
  change LinearMap.trace ℝ (Phase N)
    ((fderiv ℝ (drift 0 N) q).toLinearMap - ν • phaseLaplacian N) = _
  rw [map_sub, map_smul, ← driftDivergence_eq_linearTrace,
    driftDivergence_zero_viscosity]
  simp [smul_eq_mul]

end
end QuantumAdapter.Obligations
