import SingularClosure.SobolevTrajectoryCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Time regularity on an explicit Sobolev scale

The hypotheses contain the actual within derivative equation at every Sobolev
order, continuity of every trajectory, and smoothness of each given right-hand
side map. The conclusion follows by simultaneous finite-order induction.
No existence, derivative equation, or nonlinear smoothness premise is discharged
by this auxiliary implication.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace SingularClosure

noncomputable section

/-- Each induction step consumes two spatial Sobolev orders. -/
theorem sobolevScale_contDiffOn_nat
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (hU : ∀ m : ℕ, ContinuousOn (U m) (Ici (0 : ℝ)))
    (hF : ∀ m : ℕ, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), t ∈ Ici (0 : ℝ) →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Ici (0 : ℝ)) t)
    (n m : ℕ) : ContDiffOn ℝ n (U m) (Ici (0 : ℝ)) := by
  induction n generalizing m with
  | zero => exact contDiffOn_zero.mpr (hU m)
  | succ n ih =>
      change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (U m) (Ici (0 : ℝ))
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
      refine ⟨fun t ht => (hderiv m t ht).differentiableWithinAt, by simp, ?_⟩
      have hcomp : ContDiffOn ℝ n (fun t => F m (U (m + 2) t)) (Ici (0 : ℝ)) :=
        ((contDiff_infty.mp (hF m)) n).fun_comp_contDiffOn (ih (m + 2))
      apply hcomp.congr
      intro t ht
      exact (hderiv m t ht).derivWithin ((uniqueDiffOn_Ici 0) t ht)

/-- Explicit scale continuity and derivative equations imply all time orders. -/
theorem SOBOLEV_SCALE_TIME_SMOOTH
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (hU : ∀ m : ℕ, ContinuousOn (U m) (Ici (0 : ℝ)))
    (hF : ∀ m : ℕ, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), t ∈ Ici (0 : ℝ) →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Ici (0 : ℝ)) t) :
    ∀ m : ℕ, ContDiffOn ℝ ∞ (U m) (Ici (0 : ℝ)) := by
  intro m
  apply contDiffOn_infty.mpr
  intro n
  exact sobolevScale_contDiffOn_nat U F hU hF hderiv n m

end

end SingularClosure
