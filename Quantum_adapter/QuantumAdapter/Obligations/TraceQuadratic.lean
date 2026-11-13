import QuantumAdapter.Obligations.TraceEquivariance
import QuantumAdapter.Obligations.TraceAveraging
import QuantumAdapter.Obligations.EnergyBilinear
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
The divergence of native quadratic convection is a real linear functional.
Spatial translation invariance therefore reduces it to the actual mean.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

theorem drift_zero_viscosity_fderiv_apply (N : ℕ) (q r : Phase N) :
    fderiv ℝ (drift 0 N) q r =
      bilinearConvection N q r + bilinearConvection N r q := by
  let B := bilinearConvectionCLM N
  have hd := B.hasFDerivAt_of_bilinear (hasFDerivAt_id q) (hasFDerivAt_id q)
  have heq : (fun z : Phase N => B z z) = drift 0 N := by
    funext z
    exact bilinearConvection_self N z
  simp only [id_eq] at hd
  rw [heq] at hd
  exact congrArg (fun D : Phase N →L[ℝ] Phase N => D r) hd.fderiv

def nonlinearDivergenceCLM (N : ℕ) : Phase N →L[ℝ] ℝ :=
  ∑ i : Fin (phaseDimension N),
    (innerSL ℝ (stdOrthonormalBasis ℝ (Phase N) i)).comp
      ((bilinearConvectionCLM N).flip (stdOrthonormalBasis ℝ (Phase N) i) +
        bilinearConvectionCLM N (stdOrthonormalBasis ℝ (Phase N) i))

theorem nonlinearDivergenceCLM_apply (N : ℕ) (q : Phase N) :
    nonlinearDivergenceCLM N q = driftDivergence 0 N q := by
  simp only [nonlinearDivergenceCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, bilinearConvectionCLM_apply]
  unfold driftDivergence
  apply Finset.sum_congr rfl
  intro i hi
  simp only [drift_zero_viscosity_fderiv_apply]
  rfl

theorem nonlinearDivergenceCLM_translationInvariant (N : ℕ)
    (x : Vec) (q : Phase N) :
    nonlinearDivergenceCLM N (phaseTranslation N x q) = nonlinearDivergenceCLM N q := by
  rw [nonlinearDivergenceCLM_apply, nonlinearDivergenceCLM_apply]
  exact driftDivergence_phaseTranslation 0 N x q

theorem nonlinear_divergence_eq_mean (N : ℕ) (q : Phase N) :
    driftDivergence 0 N q = driftDivergence 0 N (meanPhase N (meanVector q)) := by
  simpa only [nonlinearDivergenceCLM_apply] using
    translationInvariant_linear_eq_mean N (nonlinearDivergenceCLM N)
      (nonlinearDivergenceCLM_translationInvariant N) q

end
end QuantumAdapter.Obligations
