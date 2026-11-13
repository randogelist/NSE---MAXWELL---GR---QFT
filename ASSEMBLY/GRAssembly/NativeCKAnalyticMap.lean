import GRAssembly.NativeCKScaledMap
import GRAssembly.NativeCKPrimitive

/-! Actual primitive operators instantiated in the analytic coefficient fixed point. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators

namespace NSEGR.NativeLiterature

noncomputable section

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def ckScaledJet (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) :
    CKSeries (CKTimeSpace E) (CKJet E V) :=
  ckScaledJetUsing (timePrimitive E V) (spatialPrimitive E V) ε p

theorem ckScaledJet_norm_le {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    {p : CKSeries (CKTimeSpace E) V} (hp : ‖p‖ ≤ 1) : ‖ckScaledJet ε p‖ ≤ 4 * ε :=
  ckScaledJetUsing_norm_le (timePrimitive E V) (spatialPrimitive E V)
    (timePrimitive_norm_le E V) (spatialPrimitive_norm_le E V) hε hε₁ hp

theorem ckScaledJet_difference_le {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (p q : CKSeries (CKTimeSpace E) V) :
    ‖ckScaledJet ε p - ckScaledJet ε q‖ ≤ 2 * ε * ‖p - q‖ :=
  ckScaledJetUsing_difference_le (timePrimitive E V) (spatialPrimitive E V)
    (timePrimitive_norm_le E V) (spatialPrimitive_norm_le E V) hε hε₁ p q

theorem ckScaledJet_eval (ε : ℝ) (p : CKSeries (CKTimeSpace E) V)
    {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    (ckScaledJet ε p).eval z =
      (ckCoefficientScale ε z,
        (ε ^ 2 • (timePrimitive E V p).eval z, ε • (spatialPrimitive E V p).eval z)) :=
  ckScaledJetUsing_eval (timePrimitive E V) (spatialPrimitive E V) ε p hz

def ckScaledCoefficientMap (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) : CKSeries (CKTimeSpace E) V :=
  ckScaledCoefficientMapUsing c (timePrimitive E V) (spatialPrimitive E V) ε p

theorem ckScaledCoefficientMap_fixedPoint
    (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    {s : ℝ} (hs : 0 < s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hεs : 4 * ε ≤ s)
    (hself : 4 * ckPositiveMajorant (fun n => c (n + 1)) s * ε ≤ 1)
    (hcontract : 2 * ckPositiveMajorant (fun n => c (n + 1)) s * ε ≤ (1 / 4 : ℝ)) :
    ∃ p : CKSeries (CKTimeSpace E) V, ‖p‖ ≤ 1 ∧ ckScaledCoefficientMap c ε p = p ∧
      ∀ q : CKSeries (CKTimeSpace E) V, ‖q‖ ≤ 1 → ckScaledCoefficientMap c ε q = q → q = p :=
  ckScaledCoefficientMapUsing_fixedPoint c hs hc (timePrimitive E V) (spatialPrimitive E V)
    (timePrimitive_norm_le E V) (spatialPrimitive_norm_le E V) hε hε₁ hεs hself hcontract

theorem ckScaledCoefficientMap_eval (g : CKRHS E V)
    (c : FormalMultilinearSeries ℝ (CKJet E V) V) (hc₀ : c 0 = 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    (hactual : ∀ y : CKJet E V, ‖y‖ ≤ s → c.sum y = g y)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hεs : 4 * ε ≤ s)
    {p : CKSeries (CKTimeSpace E) V} (hp : ‖p‖ ≤ 1)
    {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    (ckScaledCoefficientMap c ε p).eval z =
      g (ckCoefficientScale ε z,
        (ε ^ 2 • (timePrimitive E V p).eval z, ε • (spatialPrimitive E V p).eval z)) :=
  ckScaledCoefficientMapUsing_eval g c hc₀ hs hc hactual
    (timePrimitive E V) (spatialPrimitive E V) ε p
    ((ckScaledJet_norm_le hε hε₁ hp).trans hεs) hz

theorem ckAnalytic_exists_coefficient_fixedPoint {g : CKRHS E V}
    (hg : AnalyticAt ℝ g 0) (hg₀ : g 0 = 0) :
    ∃ c : FormalMultilinearSeries ℝ (CKJet E V) V, ∃ s ε : ℝ,
      0 < s ∧ c 0 = 0 ∧
      Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n) ∧
      (∀ y : CKJet E V, ‖y‖ ≤ s → c.sum y = g y) ∧
      0 < ε ∧ ε ≤ 1 ∧ 4 * ε ≤ s ∧
      ∃ p : CKSeries (CKTimeSpace E) V, ‖p‖ ≤ 1 ∧ ckScaledCoefficientMap c ε p = p ∧
        ∀ q : CKSeries (CKTimeSpace E) V, ‖q‖ ≤ 1 → ckScaledCoefficientMap c ε q = q → q = p := by
  obtain ⟨c, s, hs, hc₀, hc, hactual⟩ := ckAnalytic_superposition_data hg hg₀
  obtain ⟨ε, hε, hε₁, hεs, hp⟩ := ckScaledCoefficientMapUsing_exists_fixedPoint c hs hc
    (timePrimitive E V) (spatialPrimitive E V) (timePrimitive_norm_le E V) (spatialPrimitive_norm_le E V)
  exact ⟨c, s, ε, hs, hc₀, hc, hactual, hε, hε₁, hεs, hp⟩

end

end NSEGR.NativeLiterature
