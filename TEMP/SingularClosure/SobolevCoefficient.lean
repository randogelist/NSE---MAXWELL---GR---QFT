import SingularClosure.TorusSobolev

/-!
Generic coefficient evaluation extracted from Methlib 4813604a46179c745b82f51bee51a186e9f4cc2d,
SingularClosure/SobolevLimitBounds.lean. Exact three declaration bodies retained.
Only the generic evaluation dependency required by SmoothEvaluation is imported here.
-/

set_option autoImplicit false
set_option Elab.async true

namespace SingularClosure
noncomputable section

/-- Evaluation of an actual Fourier coefficient in any Sobolev order. -/
def torusSobolevCoeff (s : ℕ) (k : Frequency) (i : Fin 3) : TorusSobolev s →L[ℂ] ℂ :=
  ((torusSobolevWeight k : ℂ) ^ s)⁻¹ •
    ((lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 (k, i)).comp
      (torusSobolevRepr s).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem torusSobolevCoeff_apply (s : ℕ) (k : Frequency) (i : Fin 3)
    (c : TorusSobolev s) : torusSobolevCoeff s k i c = c.val k i := by
  change ((torusSobolevWeight k : ℂ) ^ s)⁻¹ *
    ((torusSobolevWeight k : ℂ) ^ s * c.val k i) = c.val k i
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero s (torusSobolevWeight_ne_zero k)), one_mul]

theorem torusSobolevCoeff_continuous (s : ℕ) (k : Frequency) (i : Fin 3) :
    Continuous (fun c : TorusSobolev s => c.val k i) := by
  exact (torusSobolevCoeff s k i).continuous.congr
    (fun c => torusSobolevCoeff_apply s k i c)


end
end SingularClosure

