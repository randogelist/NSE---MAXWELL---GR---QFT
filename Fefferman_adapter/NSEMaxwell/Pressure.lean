import NSEMaxwell.Kinematics

/-!
# Gradient of the explicit canonical pressure

The pressure decomposition determines the head potential from the pressure,
the kinetic potential, and a spatial constant. Differentiability of the head
potential is therefore not an additional hypothesis.

The canonical statement below uses only the smoothness of the reconstructed
velocity and of the canonical pressure. Both are components of the canonical
regularity endpoint in the analytic bridge.
-/

set_option autoImplicit false

open scoped ContDiff

namespace NSEMaxwell.Classical

noncomputable section

/-- Differentiating `p = h - k + C` needs regularity of `p` and `k` only. -/
theorem gradient_pressure_decomposition
    (p h k : ScalarField) (C : ℝ)
    (hp : Differentiable ℝ p) (hk : Differentiable ℝ k)
    (heq : ∀ x : Vec, p x = h x - k x + C) :
    gradient p = gradient h - gradient k := by
  have hhead : h = fun x : Vec => p x + k x - C := by
    funext x
    have hx := heq x
    linarith
  have hderiv (x : Vec) :
      fderiv ℝ h x = fderiv ℝ p x + fderiv ℝ k x := by
    rw [hhead, fderiv_sub_const, fderiv_fun_add (hp x) (hk x)]
  funext x
  apply PiLp.ext
  intro i
  change (fderiv ℝ p x) (unitVector i) =
    (fderiv ℝ h x) (unitVector i) - (fderiv ℝ k x) (unitVector i)
  rw [hderiv x]
  simp

/-- Actual pressure-gradient identity; no head-potential premise is required. -/
theorem canonicalPressure_gradient
    (ν : ℝ) (m : Vec) (B : Field)
    (hU : ContDiff ℝ ∞ (U m B))
    (hP : ContDiff ℝ ∞ (canonicalPressure ν m B)) :
    gradient (canonicalPressure ν m B) =
      gradient (scalarL (Q ν m B)) -
        gradient (fun x : Vec => ‖U m B x‖ ^ 2 / 2) := by
  have hkin : ContDiff ℝ ∞ (fun x : Vec => ‖U m B x‖ ^ 2 / 2) :=
    (hU.norm_sq ℝ).div_const 2
  apply gradient_pressure_decomposition
    (canonicalPressure ν m B) (scalarL (Q ν m B))
    (fun x : Vec => ‖U m B x‖ ^ 2 / 2)
    (scalarMean (fun x : Vec => ‖U m B x‖ ^ 2) / 2)
    (hP.differentiable (by simp)) (hkin.differentiable (by simp))
  intro x
  rfl

end

end NSEMaxwell.Classical
