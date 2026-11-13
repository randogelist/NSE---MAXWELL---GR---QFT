import QuantumAdapter.Obligations.GalerkinIntegral
import Mathlib

/-! Closed-domain differentiation and smoothness for summable derivative families. -/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations
noncomputable section

/-- A summable uniformly Lipschitz derivative family can be summed on a closed domain. -/
theorem hasFDerivWithinAt_tsum_of_dominated_lip
    {α X E : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → X → E} {f' : α → X →L[ℝ] E} {s : Set X} {x : X}
    (hx : x ∈ s) (hf : ∀ y ∈ s, Summable (fun a => ‖f a y‖))
    (hf' : Summable (fun a => ‖f' a‖))
    (b : α → ℝ) (hb : Summable b) (hb₀ : ∀ a, 0 ≤ b a)
    (hlip : ∀ a y, y ∈ s → ‖f a y - f a x‖ ≤ b a * ‖y - x‖)
    (hd : ∀ a, HasFDerivWithinAt (f a) (f' a) s x) :
    HasFDerivWithinAt (fun y => ∑' a, f a y) (∑' a, f' a) s x := by
  have hfi (y : X) (hy : y ∈ s) : Integrable (fun a => f a y) Measure.count :=
    integrable_count_iff.mpr (hf y hy)
  have hf'i : Integrable f' Measure.count := integrable_count_iff.mpr hf'
  have hbi : Integrable b Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb₀ _)] using hb
  have h := hasFDerivWithinAt_integral_of_dominated_lip hx hfi hf'i b hbi hb₀
    (Eventually.of_forall (fun a => hlip a)) (Eventually.of_forall hd)
  have heq : ∀ y ∈ s, (∫ a, f a y ∂Measure.count) = ∑' a, f a y := by
    intro y hy
    simpa only [count_real_singleton, one_smul] using integral_countable (hfi y hy)
  have hdeq : (∫ a, f' a ∂Measure.count) = ∑' a, f' a := by
    simpa only [count_real_singleton, one_smul] using integral_countable hf'i
  rw [hdeq] at h
  exact h.congr (fun y hy => (heq y hy).symm) (heq x hx).symm

/-- Convex-domain derivative bounds provide the domination needed for termwise differentiation. -/
theorem hasFDerivWithinAt_tsum_of_convex_bound
    {α X E : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → X → E} {f' : α → X → X →L[ℝ] E} {s : Set X}
    (hs : Convex ℝ s) (hf : ∀ y ∈ s, Summable (fun a => ‖f a y‖))
    (b : α → ℝ) (hb : Summable b) (hb₀ : ∀ a, 0 ≤ b a)
    (hbd : ∀ a y, y ∈ s → ‖f' a y‖ ≤ b a)
    (hd : ∀ a y, y ∈ s → HasFDerivWithinAt (f a) (f' a y) s y)
    (x : X) (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => ∑' a, f a y) (∑' a, f' a x) s x := by
  apply hasFDerivWithinAt_tsum_of_dominated_lip hx hf
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => hbd a x hx) hb)
    b hb hb₀
  · intro a y hy
    exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => hd a z hz) (fun z hz => hbd a z hz) hx hy
  · exact fun a => hd a x hx

/-- A family closed under finitely many first derivatives is smooth to every order. -/
theorem contDiffOn_of_finite_derivative_family
    {α ι X : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s : Set X) (hs : UniqueDiffOn ℝ s)
    (f : α → X → ℂ) (step : ι → α → α) (L : ι → X →L[ℝ] ℂ)
    (hd : ∀ a x, x ∈ s → HasFDerivWithinAt (f a)
      (∑ j, f (step j a) x • L j) s x) :
    ∀ a, ContDiffOn ℝ ∞ (f a) s := by
  have hfinite : ∀ n : ℕ, ∀ a, ContDiffOn ℝ n (f a) s := by
    intro n
    induction n with
    | zero =>
      intro a
      exact contDiffOn_zero.mpr (fun x hx => (hd a x hx).continuousWithinAt)
    | succ n ih =>
      intro a
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs).2
      refine ⟨by simp, (fun x => ∑ j, f (step j a) x • L j), ?_, hd a⟩
      exact ContDiffOn.sum (fun j _ => (ih (step j a)).smul contDiffOn_const)
  intro a
  exact contDiffOn_infty.mpr (fun n => hfinite n a)

end
end QuantumAdapter.Obligations
