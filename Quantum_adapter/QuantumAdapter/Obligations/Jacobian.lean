import QuantumAdapter.Obligations.JacobianMatrix
import QuantumAdapter.Dynamics

/-!
# Native phase-flow Jacobian from the actual variational equation

The only input beyond `PhaseFlow` is the displayed derivative of the actual
time-map derivative.  The variational construction must supply that input;
this theorem does not postulate a new axiom or rename the target conclusion.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Obligations

noncomputable section

variable {ν : ℝ}

theorem phaseFlow_drift_trace (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    LinearMap.trace ℝ (Phase N) (fderiv ℝ (drift ν N) q).toLinearMap =
      -phaseDecayRate ν N := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (Phase N))]
  exact F.divergence_eq N q

theorem phaseFlow_fderiv_zero (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    fderiv ℝ (F.map N 0) q = ContinuousLinearMap.id ℝ (Phase N) := by
  have hz : F.map N 0 = id := funext (F.map_zero N)
  rw [hz]
  exact (hasFDerivAt_id q).fderiv

theorem phaseFlow_jacobian_of_fderiv_variational
    (F : PhaseFlow ν)
    (hvar : ∀ (N : ℕ) (q : Phase N) (t : ℝ),
      HasDerivAt (fun s => fderiv ℝ (F.map N s) q)
        ((fderiv ℝ (drift ν N) (F.map N t q)).comp
          (fderiv ℝ (F.map N t) q)) t)
    (N : ℕ) (t : ℝ) (q : Phase N) :
    (fderiv ℝ (F.map N t) q).det = Real.exp (-(phaseDecayRate ν N) * t) := by
  apply clm_det_eq_exp_of_constant_trace
    (fun s => fderiv ℝ (F.map N s) q)
    (fun s => fderiv ℝ (drift ν N) (F.map N s q))
    (-(phaseDecayRate ν N))
  · exact fun s => hvar N q s
  · exact phaseFlow_fderiv_zero F N q
  · exact fun s => phaseFlow_drift_trace F N (F.map N s q)

end
end QuantumAdapter.Obligations
