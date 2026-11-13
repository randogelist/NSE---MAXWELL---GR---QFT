import Mathlib

/-!
Numerical and Banach fixed-point edges for the native analytic CK construction.
Every premise in these generic lemmas is explicit. The coefficient-space
construction must instantiate the displayed estimates before LI01 follows.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped Topology NNReal

namespace NSEGR.NativeLiterature

noncomputable section

/-- A positive anisotropic scaling parameter with all CK contraction budgets. -/
theorem ck_exists_scaling_budget (s L : ℝ) (hs : 0 < s) (hL : 0 ≤ L) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 4 * ε ≤ s ∧
      4 * L * ε ≤ 1 ∧ 2 * L * ε ≤ (1 / 4 : ℝ) := by
  have hden : 0 < 8 * (L + 1) := by positivity
  have hmin : 0 < min (1 : ℝ) (min (s / 8) (1 / (8 * (L + 1)))) := by
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  obtain ⟨ε, hε, hsmall⟩ := exists_between hmin
  have hεone : ε < 1 := hsmall.trans_le (min_le_left _ _)
  have hεrest : ε < min (s / 8) (1 / (8 * (L + 1))) :=
    hsmall.trans_le (min_le_right _ _)
  have hεs : ε < s / 8 := hεrest.trans_le (min_le_left _ _)
  have hεL : ε < 1 / (8 * (L + 1)) :=
    hεrest.trans_le (min_le_right _ _)
  have hεprod : ε * (8 * (L + 1)) < 1 :=
    (lt_div_iff₀ hden).mp hεL
  refine ⟨ε, hε, hεone.le, ?_, ?_, ?_⟩
  · linarith
  · nlinarith
  · nlinarith

/-- The taxicab tuple budget for the two primitive operators. -/
theorem ck_scaled_tuple_budget {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1) :
    ε ^ 2 + ε + ε ^ 2 / 2 + ε ≤ 4 * ε ∧
      ε ^ 2 / 2 + ε ≤ 2 * ε := by
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  constructor <;> nlinarith

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Banach's theorem on the closed coefficient unit ball, with literal norm bounds. -/
theorem ck_exists_unique_fixedPoint_closedUnitBall (Φ : B → B)
    (hself : ∀ x : B, ‖x‖ ≤ 1 → ‖Φ x‖ ≤ 1)
    (hcontract : ∀ x y : B, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖Φ x - Φ y‖ ≤ (1 / 4 : ℝ) * ‖x - y‖) :
    ∃ x : B, ‖x‖ ≤ 1 ∧ Φ x = x ∧
      ∀ y : B, ‖y‖ ≤ 1 → Φ y = y → y = x := by
  let S : Set B := {x | ‖x‖ ≤ 1}
  have hclosed : IsClosed S := isClosed_le continuous_norm continuous_const
  letI : CompleteSpace S := hclosed.completeSpace_coe
  letI : Nonempty S := ⟨⟨0, by simp [S]⟩⟩
  let f : S → S := fun x => ⟨Φ x, hself x x.property⟩
  have hf : ContractingWith (1 / 4 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (Φ (x : B)) (Φ (y : B)) ≤
      ((1 / 4 : ℝ≥0) : ℝ) * dist (x : B) (y : B)
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      hcontract x y x.property y.property
  let x : S := hf.fixedPoint f
  have hx : f x = x := hf.fixedPoint_isFixedPt
  refine ⟨x, x.property, congrArg Subtype.val hx, ?_⟩
  intro y hy hfy
  let yS : S := ⟨y, hy⟩
  have hyS : f yS = yS := Subtype.ext hfy
  have heq : yS = x := hf.fixedPoint_unique' hyS hx
  exact congrArg Subtype.val heq

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Explicit composition of the scaled tuple estimates with the superposition estimate. -/
theorem ck_scaled_superposition_bounds (G : H → B) (P : B → H)
    (s L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεs : 4 * ε ≤ s) (hself : 4 * L * ε ≤ 1)
    (hcontraction : 2 * L * ε ≤ (1 / 4 : ℝ))
    (hGnorm : ∀ z : H, ‖z‖ ≤ s → ‖G z‖ ≤ L * ‖z‖)
    (hGdiff : ∀ z w : H, ‖z‖ ≤ s → ‖w‖ ≤ s →
      ‖G z - G w‖ ≤ L * ‖z - w‖)
    (hPnorm : ∀ x : B, ‖x‖ ≤ 1 → ‖P x‖ ≤ 4 * ε)
    (hPdiff : ∀ x y : B, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖P x - P y‖ ≤ 2 * ε * ‖x - y‖) :
    (∀ x : B, ‖x‖ ≤ 1 → ‖G (P x)‖ ≤ 1) ∧
    (∀ x y : B, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖G (P x) - G (P y)‖ ≤ (1 / 4 : ℝ) * ‖x - y‖) := by
  constructor
  · intro x hx
    calc
      ‖G (P x)‖ ≤ L * ‖P x‖ := hGnorm (P x) ((hPnorm x hx).trans hεs)
      _ ≤ L * (4 * ε) := mul_le_mul_of_nonneg_left (hPnorm x hx) hL
      _ ≤ 1 := by nlinarith
  · intro x y hx hy
    calc
      ‖G (P x) - G (P y)‖ ≤ L * ‖P x - P y‖ :=
        hGdiff (P x) (P y) ((hPnorm x hx).trans hεs) ((hPnorm y hy).trans hεs)
      _ ≤ L * (2 * ε * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hPdiff x y hx hy) hL
      _ = (2 * L * ε) * ‖x - y‖ := by ring
      _ ≤ (1 / 4 : ℝ) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hcontraction (norm_nonneg _)

/-- The scaled coefficient map has a unique unit-ball fixed point once its
actual primitive and superposition bounds have been established. -/
theorem ck_exists_unique_scaled_fixedPoint (G : H → B) (P : B → H)
    (s L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεs : 4 * ε ≤ s) (hself : 4 * L * ε ≤ 1)
    (hcontraction : 2 * L * ε ≤ (1 / 4 : ℝ))
    (hGnorm : ∀ z : H, ‖z‖ ≤ s → ‖G z‖ ≤ L * ‖z‖)
    (hGdiff : ∀ z w : H, ‖z‖ ≤ s → ‖w‖ ≤ s →
      ‖G z - G w‖ ≤ L * ‖z - w‖)
    (hPnorm : ∀ x : B, ‖x‖ ≤ 1 → ‖P x‖ ≤ 4 * ε)
    (hPdiff : ∀ x y : B, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖P x - P y‖ ≤ 2 * ε * ‖x - y‖) :
    ∃ x : B, ‖x‖ ≤ 1 ∧ G (P x) = x ∧
      ∀ y : B, ‖y‖ ≤ 1 → G (P y) = y → y = x := by
  obtain ⟨hmap, hdiff⟩ := ck_scaled_superposition_bounds G P s L ε hL hε
    hεs hself hcontraction hGnorm hGdiff hPnorm hPdiff
  exact ck_exists_unique_fixedPoint_closedUnitBall (fun x => G (P x)) hmap hdiff

end

end NSEGR.NativeLiterature
