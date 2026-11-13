import GRAssembly.NativeCKGerm
import GRAssembly.NativeCKPrimitive
import GRAssembly.NativeCKAnalyticMap

/-! Actual primitive semantics and the exact native analytic CK existence/uniqueness theorem. -/

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

theorem ckTimePrimitive_hasDerivAt (p : CKSeries (CKTimeSpace E) V)
    {z : ℝ × E} (hz : ‖WithLp.toLp 1 z‖ < 1) :
    HasDerivAt (fun t : ℝ => ckCoordinateEval (timePrimitive E V p) (t, z.2))
      (ckCoordinateEval p z) z.1 := by
  let f : ℝ → V := fun t => p.eval (WithLp.toLp 1 (t, z.2))
  let s : Set ℝ := {t | ‖WithLp.toLp 1 (t, z.2)‖ < 1}
  have hc : Continuous (fun t : ℝ => WithLp.toLp 1 (t, z.2)) :=
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hs : IsOpen s := isOpen_lt hc.norm continuous_const
  have hcont : ∀ t ∈ s, ContinuousAt f t := by
    intro t ht
    exact (p.analyticAt ht).continuousAt.comp hc.continuousAt
  have hseg : ∀ t ∈ Set.uIcc (0 : ℝ) z.1, t ∈ s := by
    intro t ht
    have habs : |t| ≤ |z.1| := by simpa using abs_sub_left_of_mem_uIcc ht
    change ‖WithLp.toLp 1 (t, z.2)‖ < 1
    rw [WithLp.prod_norm_eq_of_L1] at hz ⊢
    simpa only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs] using
      lt_of_le_of_lt (add_le_add_right habs ‖z.2‖) hz
  have hi : IntervalIntegrable f volume 0 z.1 :=
    (continuousOn_of_forall_continuousAt (fun t ht => hcont t (hseg t ht))).intervalIntegrable
  have hm : StronglyMeasurableAtFilter f (𝓝 z.1) volume :=
    ContinuousAt.stronglyMeasurableAtFilter hs hcont z.1 hz
  have hFTC := intervalIntegral.integral_hasDerivAt_right hi hm (hcont z.1 hz)
  apply hFTC.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hz] with t ht
  exact timePrimitive_eval_eq_integral E V p ht

theorem ckTimePrimitive_initial (p : CKSeries (CKTimeSpace E) V)
    {x : E} (hx : ‖x‖ < 1) : ckCoordinateEval (timePrimitive E V p) (0, x) = 0 := by
  have hz : ‖WithLp.toLp 1 ((0 : ℝ), x)‖ < 1 := by
    simpa [WithLp.prod_norm_eq_of_L1] using hx
  rw [ckCoordinateEval, timePrimitive_eval_eq_integral E V p hz]
  simp

theorem ckTimePrimitive_initial_germ (p : CKSeries (CKTimeSpace E) V) :
    ∀ᶠ x in 𝓝 (0 : E), ckCoordinateEval (timePrimitive E V p) (0, x) = 0 := by
  have hb : ∀ᶠ x in 𝓝 (0 : E), ‖x‖ < 1 :=
    continuous_norm.continuousAt (by simpa using eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hb] with x hx
  exact ckTimePrimitive_initial p hx

theorem ckTimePrimitive_timeDerivative_germ (p : CKSeries (CKTimeSpace E) V) :
    ckTimeDerivative (ckCoordinateEval (timePrimitive E V p)) =ᶠ[𝓝 0]
      ckCoordinateEval p := by
  filter_upwards [ckCoordinate_unitBall_eventually (E := E)] with z hz
  exact (ckTimePrimitive_hasDerivAt p hz).deriv

theorem ckSpatialPrimitive_eq_spaceDerivative (p : CKSeries (CKTimeSpace E) V)
    {z : ℝ × E} (hz : ‖WithLp.toLp 1 z‖ < 1) :
    ckCoordinateEval (spatialPrimitive E V p) z =
      ckSpaceDerivative (ckCoordinateEval (timePrimitive E V p)) z := by
  rw [ckCoordinateEval, spatialPrimitive_eval_eq_fderiv E V p hz,
    ckSpaceDerivative_eq_fderiv (ckCoordinateEval_analyticAt (timePrimitive E V p) hz).differentiableAt]
  change _ = (fderiv ℝ ((timePrimitive E V p).eval ∘
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm) z).comp
      (ContinuousLinearMap.inr ℝ ℝ E)
  rw [(WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.comp_right_fderiv,
    ContinuousLinearMap.comp_assoc]
  rfl

def ckSeriesSolution (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) (z : ℝ × E) : V :=
  ε ^ 2 • (timePrimitive E V p).eval (ckInversePhysicalScale ε z)

theorem ckSeriesSolution_analyticAt (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) :
    AnalyticAt ℝ (ckSeriesSolution ε p) 0 := by
  have hp := (timePrimitive E V p).analyticAt_zero.comp_of_eq
    ((ckInversePhysicalScale (E := E) ε).analyticAt 0) (by simp)
  exact hp.const_smul

theorem ckSeriesSolution_initial_germ (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) :
    ∀ᶠ x in 𝓝 (0 : E), ckSeriesSolution ε p (0, x) = 0 := by
  have ht : Tendsto (fun x : E => ε⁻¹ • x) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_const.smul continuous_id).continuousAt.tendsto :
      Tendsto (fun x : E => ε⁻¹ • x) (𝓝 0) (𝓝 (ε⁻¹ • (0 : E))))
  filter_upwards [ht.eventually (ckTimePrimitive_initial_germ p)] with x hx
  simpa [ckSeriesSolution, ckInversePhysicalScale_apply, ckCoordinateEval] using
    congrArg (fun v : V => ε ^ 2 • v) hx

theorem ckSeriesSolution_timeDerivative (ε : ℝ) (hε : ε ≠ 0)
    (p : CKSeries (CKTimeSpace E) V) {z : ℝ × E}
    (hz : ‖ckInversePhysicalScale ε z‖ < 1) :
    ckTimeDerivative (ckSeriesSolution ε p) z = p.eval (ckInversePhysicalScale ε z) := by
  have hpoint : ‖WithLp.toLp 1 ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)‖ < 1 := hz
  have hA := ckTimePrimitive_hasDerivAt p hpoint
  have hscaled := hA.scomp z.1 ((hasDerivAt_id z.1).const_mul ((ε ^ 2)⁻¹))
  have hfinal := hscaled.const_smul (ε ^ 2)
  simpa [ckTimeDerivative, ckSeriesSolution, ckInversePhysicalScale_apply,
    ckCoordinateEval, Function.comp_def, smul_smul, ← mul_assoc, hε, pow_ne_zero 2 hε]
      using hfinal.deriv

theorem ckSeriesSolution_spaceDerivative (ε : ℝ)
    (p : CKSeries (CKTimeSpace E) V) {z : ℝ × E}
    (hz : ‖ckInversePhysicalScale ε z‖ < 1) :
    ckSpaceDerivative (ckSeriesSolution ε p) z =
      ε ^ 2 • (ckSpaceDerivative (ckCoordinateEval (timePrimitive E V p))
        ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ E) := by
  have hpoint : ‖WithLp.toLp 1 ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)‖ < 1 := hz
  have hA := (ckCoordinateEval_analyticAt (timePrimitive E V p) hpoint).curry_right.differentiableAt
  have hx := (hasFDerivAt_id (𝕜 := ℝ) z.2).const_smul ε⁻¹
  have hscaled := hA.hasFDerivAt.comp z.2 hx
  simpa [ckSpaceDerivative, ckSeriesSolution, ckInversePhysicalScale_apply,
    ckCoordinateEval, Function.comp_def] using (hscaled.const_smul (ε ^ 2)).fderiv

theorem ckSeriesSolution_spaceDerivative_eq (ε : ℝ) (hε : ε ≠ 0)
    (p : CKSeries (CKTimeSpace E) V) {z : ℝ × E}
    (hz : ‖ckInversePhysicalScale ε z‖ < 1) :
    ckSpaceDerivative (ckSeriesSolution ε p) z =
      ε • (spatialPrimitive E V p).eval (ckInversePhysicalScale ε z) := by
  rw [ckSeriesSolution_spaceDerivative ε p hz]
  have hpoint : ‖WithLp.toLp 1 ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)‖ < 1 := hz
  rw [← ckSpatialPrimitive_eq_spaceDerivative p hpoint]
  have heq : ε ^ 2 * ε⁻¹ = ε := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hε, mul_one]
  ext x
  simp [ContinuousLinearMap.comp_apply, map_smul, smul_smul, heq,
    ckCoordinateEval, ckInversePhysicalScale_apply]

theorem ckScaledSolution_eq_timePrimitive {g : CKRHS E V}
    {w : ℝ × E → V} (hw : CKNormalizedSolution g w) (ε : ℝ)
    (p : CKSeries (CKTimeSpace E) V)
    (hp : p.eval =ᶠ[𝓝 0] ckTimeDerivative w ∘ ckPhysicalScale ε) :
    ckScaledSolution ε w =ᶠ[𝓝 0]
      (fun z => ε ^ 2 • ckCoordinateEval (timePrimitive E V p) z) := by
  have hA := ckCoordinateEval_analyticAt_zero (timePrimitive E V p)
  apply ckGerm_eq_of_timeDerivative_eq (ckScaledSolution_analyticAt hw.analytic ε)
    (hA.const_smul (c := ε ^ 2))
  · have hx : Tendsto (fun x : E => ε • x) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_const.smul continuous_id).continuousAt.tendsto :
        Tendsto (fun x : E => ε • x) (𝓝 0) (𝓝 (ε • (0 : E))))
    filter_upwards [hx.eventually hw.initial, ckTimePrimitive_initial_germ p] with x hx hAx
    simp only [ckScaledSolution, mul_zero, hx, hAx, smul_zero]
  · have hcoord : Tendsto (WithLp.toLp 1 : ℝ × E → CKTimeSpace E) (𝓝 0) (𝓝 0) := by
      simpa using (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.continuous.continuousAt.tendsto
    have hscale : Tendsto (fun z : ℝ × E => (ε ^ 2 * z.1, ε • z.2)) (𝓝 0) (𝓝 0) := by
      have ht : Tendsto (ckPhysicalScale (E := E) ε) (𝓝 0) (𝓝 0) := by
        simpa using (ckPhysicalScale (E := E) ε).continuous.continuousAt.tendsto
      exact ht.comp hcoord
    filter_upwards [hscale.eventually hw.analytic.eventually_analyticAt,
      hcoord.eventually hp, ckCoordinate_unitBall_eventually (E := E)] with z hzw hzp hz
    rw [ckScaledSolution_timeDerivative ε z hzw.curry_left.differentiableAt]
    have hAd := (ckTimePrimitive_hasDerivAt p hz).const_smul (ε ^ 2)
    change _ = deriv (fun t => ε ^ 2 • ckCoordinateEval (timePrimitive E V p) (t, z.2)) z.1
    rw [hAd.deriv]
    exact congrArg (fun v : V => ε ^ 2 • v) hzp.symm

theorem ckNormalizedSolution_eq_seriesSolution {g : CKRHS E V}
    {w : ℝ × E → V} (hw : CKNormalizedSolution g w) (ε : ℝ) (hε : ε ≠ 0)
    (p : CKSeries (CKTimeSpace E) V)
    (hp : p.eval =ᶠ[𝓝 0] ckTimeDerivative w ∘ ckPhysicalScale ε) :
    w =ᶠ[𝓝 0] ckSeriesSolution ε p := by
  have hrec := ckScaledSolution_eq_timePrimitive hw ε p hp
  have hcoord : Tendsto (WithLp.ofLp : CKTimeSpace E → ℝ × E) (𝓝 0) (𝓝 0) := by
    simpa using (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).continuous.continuousAt.tendsto
  apply ckGerm_eq_of_physicalScale ε hε
  filter_upwards [hcoord.eventually hrec] with z hz
  change w (ckPhysicalScale ε z) = ckSeriesSolution ε p (ckPhysicalScale ε z)
  rw [ckSeriesSolution, ckPhysicalScale_leftInverse ε hε]
  exact hz

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
    simpa using (ckPhysicalScale (E := E) ε).continuous.continuousAt.tendsto
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
