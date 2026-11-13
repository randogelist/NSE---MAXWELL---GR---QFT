import QuantumAdapter.Obligations.TraceQuadratic

/-!
The real divergence of the actual full Fourier convection vanishes. The
algebraic polarization step uses only its native energy cancellation and
its exact frozen mean; no Hamiltonian structure is postulated.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

theorem quadratic_energy_linearization_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E)
    (henergy : ∀ z : E, inner ℝ z (B z z) = 0)
    (m : E) (hmean : ∀ z : E, inner ℝ m (B z z) = 0) (h : E) :
    inner ℝ h (B m h + B h m) = 0 := by
  have hp := henergy (m + h)
  have hn := henergy (m - h)
  have hm := henergy m
  have ha := hmean h
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right] at hp hn
  rw [inner_add_right]
  linarith

theorem drift_zero_viscosity_fderiv_mean_orthogonal
    (N : ℕ) (m : Vec) (h : Phase N) :
    inner ℝ h (fderiv ℝ (drift 0 N) (meanPhase N m) h) = 0 := by
  rw [drift_zero_viscosity_fderiv_apply]
  apply quadratic_energy_linearization_orthogonal (bilinearConvectionCLM N)
  · intro z
    simpa only [bilinearConvectionCLM_apply, bilinearConvection_self] using
      inner_self_drift_zero N z
  · intro z
    simpa only [bilinearConvectionCLM_apply, bilinearConvection_self] using
      inner_mean_drift_zero 0 N m z

theorem driftDivergence_zero_viscosity_mean (N : ℕ) (m : Vec) :
    driftDivergence 0 N (meanPhase N m) = 0 := by
  unfold driftDivergence
  simp only [drift_zero_viscosity_fderiv_mean_orthogonal, Finset.sum_const_zero]

theorem driftDivergence_zero_viscosity (N : ℕ) (q : Phase N) :
    driftDivergence 0 N q = 0 := by
  rw [nonlinear_divergence_eq_mean, driftDivergence_zero_viscosity_mean]

end
end QuantumAdapter.Obligations
