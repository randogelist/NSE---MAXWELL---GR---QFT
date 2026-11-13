import NSEMaxwell.Spacetime
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
Continuous derivative jets on the closure of a convex open set give genuine
within derivatives and all finite smoothness orders. No negative-time
extension and no analytic-order hypothesis is used.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open Set Filter
open scoped ContDiff Topology

noncomputable section

section BoundaryDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous derivative field on the closed domain determines the within
derivative there from its actual interior derivative. -/
theorem hasFDerivWithinAt_closure_of_continuous_jets
    {s : Set E} (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    {f : E → F} {f' : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closure s))
    (hf' : ContinuousOn f' (closure s))
    (hderiv : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    {x : E} (hx : x ∈ closure s) :
    HasFDerivWithinAt f (f' x) (closure s) x := by
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
    hsConvex hsOpen
    (fun y hy => (hf y hy).mono subset_closure)
  have hlimit : Tendsto f' (𝓝[s] x) (𝓝 (f' x)) :=
    (hf' x hx).mono subset_closure
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hderiv y hy).fderiv.symm

end BoundaryDerivative

section JetTower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]

/-- Finite smoothness from a compatible tower of continuous within derivative
jets. `C` is the continuous linear currying map between successive jet spaces. -/
theorem contDiffOn_nat_of_compatible_jets
    {s : Set E} (hs : UniqueDiffOn ℝ s)
    (J : ∀ n, E → F n)
    (C : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hcont : ∀ n, ContinuousOn (J n) s)
    (hderiv : ∀ n x, x ∈ s →
      HasFDerivWithinAt (J n) (C n (J (n + 1) x)) s x)
    (k q : ℕ) : ContDiffOn ℝ k (J q) s := by
  induction k generalizing q with
  | zero =>
      exact contDiffOn_zero.mpr (hcont q)
  | succ k ih =>
      have hsucc : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (J q) s := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs).2
        refine ⟨by simp, fun x => C q (J (q + 1) x), ?_, ?_⟩
        · exact (C q).contDiff.fun_comp_contDiffOn (ih (q + 1))
        · exact hderiv q
      simpa using hsucc

/-- Every jet in a compatible continuous derivative tower is infinitely
smooth on the same unique-differentiability domain. -/
theorem contDiffOn_infty_of_compatible_jets
    {s : Set E} (hs : UniqueDiffOn ℝ s)
    (J : ∀ n, E → F n)
    (C : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hcont : ∀ n, ContinuousOn (J n) s)
    (hderiv : ∀ n x, x ∈ s →
      HasFDerivWithinAt (J n) (C n (J (n + 1) x)) s x)
    (q : ℕ) : ContDiffOn ℝ ∞ (J q) s := by
  apply contDiffOn_infty.mpr
  intro k
  exact contDiffOn_nat_of_compatible_jets hs J C hcont hderiv k q

/-- Interior derivative identities and continuity of all jets extend smoothness
to the closure. The conclusion includes boundary points. -/
theorem contDiffOn_closure_of_continuous_jets
    {s : Set E} (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    (hsUnique : UniqueDiffOn ℝ (closure s))
    (J : ∀ n, E → F n)
    (C : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hcont : ∀ n, ContinuousOn (J n) (closure s))
    (hderiv : ∀ n x, x ∈ s →
      HasFDerivAt (J n) (C n (J (n + 1) x)) x)
    (q : ℕ) : ContDiffOn ℝ ∞ (J q) (closure s) := by
  apply contDiffOn_infty_of_compatible_jets hsUnique J C hcont
  intro n x hx
  exact hasFDerivWithinAt_closure_of_continuous_jets hsOpen hsConvex
    (hcont n) ((C n).continuous.comp_continuousOn (hcont (n + 1)))
    (hderiv n) hx

end JetTower

section ForwardSpacetime

open NSEMaxwell.Classical NSEMaxwell.Spacetime

/-- The positive-time interior of the fixed forward spacetime. -/
def positiveSpacetime : Set (ℝ × Vec) := Ioi (0 : ℝ) ×ˢ (univ : Set Vec)

theorem isOpen_positiveSpacetime : IsOpen positiveSpacetime :=
  isOpen_Ioi.prod isOpen_univ

theorem convex_positiveSpacetime : Convex ℝ positiveSpacetime :=
  (convex_Ioi (0 : ℝ)).prod convex_univ

theorem closure_positiveSpacetime : closure positiveSpacetime = forwardSpacetime := by
  rw [positiveSpacetime, closure_prod_eq, forwardSpacetime_eq_prod]
  simp

variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]

/-- The exact closed-halfspace specialization used for Fourier parameter jets. -/
theorem contDiffOn_forwardSpacetime_of_continuous_jets
    (J : ∀ n, (ℝ × Vec) → F n)
    (C : ∀ n, F (n + 1) →L[ℝ] ((ℝ × Vec) →L[ℝ] F n))
    (hcont : ∀ n, ContinuousOn (J n) forwardSpacetime)
    (hderiv : ∀ n x, x ∈ positiveSpacetime →
      HasFDerivAt (J n) (C n (J (n + 1) x)) x)
    (q : ℕ) : ContDiffOn ℝ ∞ (J q) forwardSpacetime := by
  have hUnique : UniqueDiffOn ℝ (closure positiveSpacetime) := by
    rw [closure_positiveSpacetime]
    exact uniqueDiffOn_forwardSpacetime
  have hcont' : ∀ n, ContinuousOn (J n) (closure positiveSpacetime) := by
    simpa only [closure_positiveSpacetime] using hcont
  simpa only [closure_positiveSpacetime] using
    contDiffOn_closure_of_continuous_jets isOpen_positiveSpacetime
      convex_positiveSpacetime hUnique J C hcont' hderiv q

end ForwardSpacetime

end

end NSEMaxwell.HodgeProof
