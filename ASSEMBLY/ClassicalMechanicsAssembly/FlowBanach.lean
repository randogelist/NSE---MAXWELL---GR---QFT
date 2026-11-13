import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

/-!
Banach-space edges of the finite-slab flow construction.

The factorial estimate is an explicit hypothesis: this module does not identify
an arbitrary operator with the Volterra operator. Likewise, the superposition
smoothness and residual derivative needed by the implicit-function step remain
explicit until the concrete path-space estimates are discharged.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open scoped Topology ContDiff
open Filter

noncomputable section

section OperatorSeries

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Factorial power bounds imply convergence in the operator norm. -/
theorem summable_operator_powers_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    Summable (fun n : ℕ => L ^ n) := by
  exact (Real.summable_pow_div_factorial C).of_norm_bounded hbound

/-- The convergent power series is a two-sided inverse; no smallness condition is used. -/
theorem operator_series_inverse_identities_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    (1 - L) * (∑' n : ℕ, L ^ n) = 1 ∧
      (∑' n : ℕ, L ^ n) * (1 - L) = 1 := by
  have hs := summable_operator_powers_of_factorial_bound L C hbound
  exact ⟨hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩

/-- The actual operator `1 - L` is a Banach-space isomorphism. -/
theorem one_sub_operator_isInvertible_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    (1 - L).IsInvertible := by
  obtain ⟨hleft, hright⟩ :=
    operator_series_inverse_identities_of_factorial_bound L C hbound
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := ∑' n : ℕ, L ^ n)
  · change (1 - L) * (∑' n : ℕ, L ^ n) = 1
    exact hleft
  · change (∑' n : ℕ, L ^ n) * (1 - L) = 1
    exact hright

/-- Identification of the library's total inverse with the convergent series. -/
theorem operator_inverse_eq_tsum_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    (1 - L).inverse = ∑' n : ℕ, L ^ n := by
  obtain ⟨hleft, hright⟩ :=
    operator_series_inverse_identities_of_factorial_bound L C hbound
  apply ContinuousLinearMap.inverse_eq
  · change (1 - L) * (∑' n : ℕ, L ^ n) = 1
    exact hleft
  · change (∑' n : ℕ, L ^ n) * (1 - L) = 1
    exact hright

end OperatorSeries

section ImplicitBranch

variable {E B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- A chosen unique root agrees locally with the smooth implicit branch.
No continuity or differentiability of the chosen root is assumed. -/
theorem contDiff_of_unique_implicit_branch
    (Φ : E × B → B) (Γ : E → B)
    (hΦ : ContDiff ℝ ∞ Φ)
    (hroot : ∀ a, Φ (a, Γ a) = 0)
    (hunique : ∀ a b, Φ (a, b) = 0 → b = Γ a)
    (hinv : ∀ a, (fderiv ℝ Φ (a, Γ a) ∘L
      ContinuousLinearMap.inr ℝ E B).IsInvertible) :
    ContDiff ℝ ∞ Γ := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  have hc : ContDiffAt ℝ ∞ Φ (a, Γ a) := hΦ.contDiffAt
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hψ := hc.contDiffAt_implicitFunction hn (hinv a)
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hc.eventually_apply_implicitFunction hn (hinv a)] with b hb
  exact (hunique b _ (by simpa only [hroot a] using hb)).symm

/-- Volterra/IFT composition with the actual residual partial derivative exposed.
The two unresolved analytic inputs are residual smoothness and factorial bounds. -/
theorem contDiff_of_unique_volterra_residual
    (Φ : E × B → B) (Γ : E → B) (L : E → B →L[ℝ] B) (C : E → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ)
    (hroot : ∀ a, Φ (a, Γ a) = 0)
    (hunique : ∀ a b, Φ (a, b) = 0 → b = Γ a)
    (hpartial : ∀ a, fderiv ℝ Φ (a, Γ a) ∘L
      ContinuousLinearMap.inr ℝ E B = 1 - L a)
    (hbound : ∀ a (n : ℕ), ‖L a ^ n‖ ≤ C a ^ n / (n.factorial : ℝ)) :
    ContDiff ℝ ∞ Γ := by
  apply contDiff_of_unique_implicit_branch Φ Γ hΦ hroot hunique
  intro a
  rw [hpartial a]
  exact one_sub_operator_isInvertible_of_factorial_bound (L a) (C a) (hbound a)

end ImplicitBranch

section Superposition

variable {I E : Type*} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual path superposition on a compact time domain. -/
def flowPathSuperposition (u : C(I × E, E)) (γ : C(I, E)) : C(I, E) :=
  u.comp ((ContinuousMap.id I).prodMk γ)

@[simp]
theorem flowPathSuperposition_apply (u : C(I × E, E)) (γ : C(I, E)) (t : I) :
    flowPathSuperposition u γ t = u (t, γ t) := rfl

/-- Uniform spatial Lipschitz control passes to the actual sup-norm path map. -/
theorem flowPathSuperposition_lipschitz (u : C(I × E, E)) (K : ℝ≥0)
    (hu : ∀ t : I, LipschitzWith K (fun x => u (t, x))) :
    LipschitzWith K (flowPathSuperposition u) := by
  apply LipschitzWith.of_dist_le_mul
  intro γ δ
  apply (ContinuousMap.dist_le (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro t
  exact ((hu t).dist_le_mul (γ t) (δ t)).trans
    (mul_le_mul_of_nonneg_left
      (ContinuousMap.dist_apply_le_dist (f := γ) (g := δ) t) K.coe_nonneg)

end Superposition

end

end ClassicalMechanicsAssembly
