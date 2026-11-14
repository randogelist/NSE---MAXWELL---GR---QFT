import SingularClosure.TorusSobolev
import SingularClosure.FiniteHessian

/-!
# Generic Fourier multiplier bounds

Exact declaration extractions from Methlib commit
4813604a46179c745b82f51bee51a186e9f4cc2d:
`TorusGalerkinSobolev.torusSobolevWeight_sq` and
`HighOrderEstimate.derivativeSymbol_norm_le_weight`.
The Galerkin trajectory imports are absent; both preserved bodies use only
actual frequency algebra, the native weight, and the existing Hessian identity.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace SingularClosure
noncomputable section

theorem torusSobolevWeight_sq (k : Frequency) :
    torusSobolevWeight k ^ 2 =
      1 + (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) := by
  unfold torusSobolevWeight
  apply Real.sq_sqrt
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  positivity

theorem derivativeSymbol_norm_le_weight (k : Frequency) (j : Fin 3) :
    ‖derivativeSymbol j k‖ ≤ torusSobolevWeight k := by
  have hn : ‖derivativeSymbol j k‖ ^ 2 = (2 * Real.pi * (k j : ℝ)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [derivativeSymbol, Complex.normSq_apply, pow_two]
  have hs : (2 * Real.pi * (k j : ℝ)) ^ 2 ≤ laplacianFrequency k := by
    rw [← sum_derivativeScale_sq]
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun i : Fin 3 => (2 * Real.pi * (k i : ℝ)) ^ 2)
      (fun i _ => sq_nonneg (2 * Real.pi * (k i : ℝ))) (Finset.mem_univ j)
  apply (sq_le_sq₀ (norm_nonneg _) (torusSobolevWeight_pos k).le).mp
  rw [hn, torusSobolevWeight_sq]
  unfold laplacianFrequency at hs
  linarith

end
end SingularClosure
