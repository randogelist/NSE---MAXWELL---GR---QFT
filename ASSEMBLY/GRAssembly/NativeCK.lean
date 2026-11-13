import GRAssembly.NativeCKSemantics
import GRAssembly.NativeCKAnalyticMap

/-! Exact native analytic CK existence and arbitrary analytic-germ uniqueness. -/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NSEGR.NativeLiterature

noncomputable section

variable {E V Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem ckSeriesSolution_isSolution [CompleteSpace E]
    (g : CKRHS E V) (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    (hc₀ : c 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    (hactual : ∀ y : CKJet E V, ‖y‖ ≤ s → c.sum y = g y)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hεs : 4 * ε ≤ s)
    (p : CKSeries (CKTimeSpace E) V) (hp : ‖p‖ ≤ 1)
    (hfixed : ckScaledCoefficientMap c ε p = p) :
    CKNormalizedSolution g (ckSeriesSolution ε p) := by
  refine ⟨ckSeriesSolution_analyticAt ε p, ckSeriesSolution_initial_germ ε p, ?_⟩
  filter_upwards [ckInversePhysicalScale_unitBall_eventually (E := E) ε] with z hz
  change ckTimeDerivative (ckSeriesSolution ε p) z =
    g (z, (ckSeriesSolution ε p z, ckSpaceDerivative (ckSeriesSolution ε p) z))
  rw [ckSeriesSolution_timeDerivative ε hε.ne' p hz,
    ckSeriesSolution_spaceDerivative_eq ε hε.ne' p hz]
  have heval := ckScaledCoefficientMap_eval g c hc₀ hs hc hactual hε.le hε₁ hεs hp hz
  rw [hfixed] at heval
  change p.eval (ckInversePhysicalScale ε z) =
    g (ckPhysicalScale ε (ckInversePhysicalScale ε z),
      (ckSeriesSolution ε p z, ε • (spatialPrimitive E V p).eval (ckInversePhysicalScale ε z))) at heval
  simpa only [ckPhysicalScale_rightInverse ε hε.ne'] using heval

theorem ck_normalized_solution_exists [CompleteSpace E]
    (g : CKRHS E V) (hg : AnalyticAt ℝ g 0) (hg₀ : g 0 = 0) :
    ∃ w : ℝ × E → V, CKNormalizedSolution g w := by
  obtain ⟨c, s, ε, hs, hc₀, hc, hactual, hε, hε₁, hεs, p, hp, hfixed, _⟩ :=
    ckAnalytic_exists_coefficient_fixedPoint hg hg₀
  exact ⟨ckSeriesSolution ε p,
    ckSeriesSolution_isSolution g c hc₀ hs.le hc hactual hε hε₁ hεs p hp hfixed⟩

theorem ckSeriesSolution_fixedPoint [CompleteSpace E]
    (g : CKRHS E V) (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    (hc₀ : c 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    (hactual : ∀ y : CKJet E V, ‖y‖ ≤ s → c.sum y = g y)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hεs : 4 * ε ≤ s)
    (p : CKSeries (CKTimeSpace E) V) (hp : ‖p‖ ≤ 1)
    (hsol : CKNormalizedSolution g (ckSeriesSolution ε p)) :
    ckScaledCoefficientMap c ε p = p := by
  apply CKSeries.eq_of_eval_eventuallyEq
  have ht : Tendsto (ckPhysicalScale (E := E) ε) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using
      ((ckPhysicalScale (E := E) ε).continuous.continuousAt (x := (0 : CKTimeSpace E))).tendsto
  have hb : ∀ᶠ z : CKTimeSpace E in 𝓝 0, ‖z‖ < 1 := by
    simpa using Metric.ball_mem_nhds (0 : CKTimeSpace E) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [ht.eventually hsol.equation, hb] with z heq hz
  have hiz : ‖ckInversePhysicalScale ε (ckPhysicalScale ε z)‖ < 1 := by
    simpa only [ckPhysicalScale_leftInverse ε hε.ne'] using hz
  change ckTimeDerivative (ckSeriesSolution ε p) (ckPhysicalScale ε z) =
    g (ckPhysicalScale ε z, (ckSeriesSolution ε p (ckPhysicalScale ε z),
      ckSpaceDerivative (ckSeriesSolution ε p) (ckPhysicalScale ε z))) at heq
  rw [ckSeriesSolution_timeDerivative ε hε.ne' p hiz,
    ckSeriesSolution_spaceDerivative_eq ε hε.ne' p hiz,
    ckPhysicalScale_leftInverse ε hε.ne'] at heq
  rw [ckScaledCoefficientMap_eval g c hc₀ hs hc hactual hε.le hε₁ hεs hp hz]
  symm
  simpa only [ckSeriesSolution, ckPhysicalScale_leftInverse ε hε.ne'] using heq

theorem ckTimeSeries_fixedPoint [CompleteSpace E]
    (g : CKRHS E V) (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    (hc₀ : c 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    (hactual : ∀ y : CKJet E V, ‖y‖ ≤ s → c.sum y = g y)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hεs : 4 * ε ≤ s)
    {w : ℝ × E → V} (hw : CKNormalizedSolution g w)
    (p : CKSeries (CKTimeSpace E) V) (hp : ‖p‖ ≤ 1)
    (hrep : p.eval =ᶠ[𝓝 0] ckTimeDerivative w ∘ ckPhysicalScale ε) :
    ckScaledCoefficientMap c ε p = p :=
  ckSeriesSolution_fixedPoint g c hc₀ hs hc hactual hε hε₁ hεs p hp
    (ckNormalizedSolution_congr hw (ckNormalizedSolution_eq_seriesSolution hw ε hε.ne' p hrep))

theorem ck_normalized_solution_unique [CompleteSpace E]
    (g : CKRHS E V) (hg : AnalyticAt ℝ g 0) (hg₀ : g 0 = 0)
    {w v : ℝ × E → V} (hw : CKNormalizedSolution g w)
    (hv : CKNormalizedSolution g v) : w =ᶠ[𝓝 0] v := by
  obtain ⟨c, s, hs, hc₀, hc, hactual⟩ := ckAnalytic_superposition_data hg hg₀
  obtain ⟨δw, hδw, hsw⟩ := ckNormalizedSolution_small_timeSeries hw hg₀
  obtain ⟨δv, hδv, hsv⟩ := ckNormalizedSolution_small_timeSeries hv hg₀
  obtain ⟨ε, hε, hεδ, hε₁, hεs, hself, hcontract⟩ :=
    ck_exists_scaling_budget_lt s (ckPositiveMajorant (fun n => c (n + 1)) s)
      (min δw δv) hs (ckPositiveMajorant_nonneg _ hs.le) (lt_min hδw hδv)
  obtain ⟨pw, hpw, hrepw⟩ := hsw ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  obtain ⟨pv, hpv, hrepv⟩ := hsv ε hε (lt_of_lt_of_le hεδ (min_le_right _ _))
  obtain ⟨p, _, _, huniq⟩ := ckScaledCoefficientMap_fixedPoint c hs hc
    hε hε₁ hεs hself hcontract
  have heqw : pw = p := huniq pw hpw.le
    (ckTimeSeries_fixedPoint g c hc₀ hs.le hc hactual hε hε₁ hεs hw pw hpw.le hrepw)
  have heqv : pv = p := huniq pv hpv.le
    (ckTimeSeries_fixedPoint g c hc₀ hs.le hc hactual hε hε₁ hεs hv pv hpv.le hrepv)
  exact ckNormalizedSolution_eq_of_timeSeries hw hv ε hε.ne' pw pv hrepw hrepv
    (heqw.trans heqv.symm)

theorem ck_normalized_exists_unique [CompleteSpace E]
    (g : CKRHS E V) (hg : AnalyticAt ℝ g 0) (hg₀ : g 0 = 0) :
    ∃ w : ℝ × E → V, CKNormalizedSolution g w ∧
      ∀ v : ℝ × E → V, CKNormalizedSolution g v → w =ᶠ[𝓝 0] v := by
  obtain ⟨w, hw⟩ := ck_normalized_solution_exists g hg hg₀
  exact ⟨w, hw, fun v hv => ck_normalized_solution_unique g hg hg₀ hw hv⟩

theorem ckLocal_exists_unique [CompleteSpace E]
    (F : CKRHS E V) (u₀ : E → V) (t₀ : ℝ) (x₀ : E)
    (hu₀ : AnalyticAt ℝ u₀ x₀)
    (hF : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀)) :
    ∃ u : ℝ × E → V, CKLocalSolution F u₀ t₀ x₀ u ∧
      ∀ v : ℝ × E → V, CKLocalSolution F u₀ t₀ x₀ v → u =ᶠ[𝓝 (t₀, x₀)] v :=
  ckLocal_exists_unique_of_normalized ck_normalized_exists_unique F u₀ t₀ x₀ hu₀ hF

theorem literatureAnalyticCKInput_native : LiteratureAnalyticCKInput :=
  literatureAnalyticCKInput_of_normalized
    (fun _n _m _hn _hm g hg hg₀ => ck_normalized_exists_unique g hg hg₀)

end

end NSEGR.NativeLiterature
