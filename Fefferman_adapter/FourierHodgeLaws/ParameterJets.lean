import FourierHodgeLaws.ClosedHalfspaceSmooth
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
Summation of compatible derivative jets on a closed convex domain.
All summability and derivative assumptions are explicit analytic estimates;
the conclusion is actual within smoothness of the actual `tsum`.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open Set Filter
open scoped BigOperators ContDiff Topology

noncomputable section

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]

/-- A normally convergent compatible derivative tower is smooth through the
boundary of its convex open domain. -/
theorem contDiffOn_tsum_closure_of_compatible_jets
    {s : Set E} (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    (hsUnique : UniqueDiffOn ℝ (closure s))
    (J : ∀ n, ι → E → F n)
    (C : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (u : ℕ → ι → ℝ)
    (hu : ∀ n, Summable (u n))
    (hbound : ∀ n i x, x ∈ closure s → ‖J n i x‖ ≤ u n i)
    (hcont : ∀ n i, ContinuousOn (J n i) (closure s))
    (hderiv : ∀ n i x, x ∈ s →
      HasFDerivAt (J n i) (C n (J (n + 1) i x)) x)
    (q : ℕ) : ContDiffOn ℝ ∞ (fun x => ∑' i, J q i x) (closure s) := by
  let A : ∀ n, E → F n := fun n x => ∑' i, J n i x
  have hsum (n : ℕ) (x : E) (hx : x ∈ closure s) :
      Summable (fun i => J n i x) :=
    (hu n).of_norm_bounded (fun i => hbound n i x hx)
  have hAcont (n : ℕ) : ContinuousOn (A n) (closure s) :=
    continuousOn_tsum (hcont n) (hu n) (hbound n)
  have hAderiv (n : ℕ) (x : E) (hx : x ∈ s) :
      HasFDerivAt (A n) (C n (A (n + 1) x)) x := by
    have hdBound (i : ι) (y : E) (hy : y ∈ s) :
        ‖C n (J (n + 1) i y)‖ ≤ ‖C n‖ * u (n + 1) i :=
      (C n).le_opNorm_of_le (hbound (n + 1) i y (subset_closure hy))
    have hD := hasFDerivAt_tsum_of_isPreconnected
      ((hu (n + 1)).mul_left ‖C n‖) hsOpen hsConvex.isPreconnected
      (hderiv n) hdBound hx (hsum n x (subset_closure hx)) hx
    rw [← (C n).map_tsum (hsum (n + 1) x (subset_closure hx))] at hD
    exact hD
  exact contDiffOn_closure_of_continuous_jets hsOpen hsConvex hsUnique
    A C hAcont hAderiv q

end

end NSEMaxwell.HodgeProof
