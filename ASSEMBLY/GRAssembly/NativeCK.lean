import GRAssembly.NativeCKNormalization
import GRAssembly.NativeCKSeries
import GRAssembly.NativeCKPrimitive
import GRAssembly.NativeCKAnalyticMap
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Exact specialization from generic analytic CK solutions to the literal
finite-dimensional literature signature. The normalized existence/uniqueness
premise in the transport theorem is explicit; it is not an axiom declaration.
-/

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

def ckCoordinateEval (p : CKSeries (CKTimeSpace E) V) (z : ℝ × E) : V :=
  p.eval (WithLp.toLp 1 z)

theorem ckCoordinateEval_analyticAt (p : CKSeries (CKTimeSpace E) V)
    {z : ℝ × E} (hz : ‖WithLp.toLp 1 z‖ < 1) :
    AnalyticAt ℝ (ckCoordinateEval p) z :=
  (p.analyticAt hz).comp
    ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.toContinuousLinearMap.analyticAt z)

theorem ckCoordinateEval_analyticAt_zero (p : CKSeries (CKTimeSpace E) V) :
    AnalyticAt ℝ (ckCoordinateEval p) 0 := by
  apply ckCoordinateEval_analyticAt
  simp

theorem ckCoordinate_unitBall_eventually :
    ∀ᶠ z : ℝ × E in 𝓝 0, ‖WithLp.toLp 1 z‖ < 1 := by
  have ht := (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.continuous.norm.continuousAt
  exact ht (by simpa using eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))

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

/-- Physical coordinates for the anisotropic CK rescaling. -/
def ckPhysicalScale (ε : ℝ) : CKTimeSpace E →L[ℝ] ℝ × E :=
  ((ε ^ 2) • WithLp.fstL 1 ℝ ℝ E).prod (ε • WithLp.sndL 1 ℝ ℝ E)

@[simp] theorem ckPhysicalScale_apply (ε : ℝ) (z : CKTimeSpace E) :
    ckPhysicalScale (E := E) ε z = (ε ^ 2 * z.fst, ε • z.snd) := rfl

theorem ckPhysicalScale_norm_le (ε : ℝ) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ‖ckPhysicalScale (E := E) ε‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro z
  rw [ckPhysicalScale_apply, Prod.norm_def]
  apply max_le
  · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg ε)]
    have hε² : ε ^ 2 ≤ ε := by nlinarith
    exact (mul_le_mul_of_nonneg_right hε² (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le z) hε)
  · rw [norm_smul, Real.norm_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (WithLp.norm_snd_le z) hε

def ckInversePhysicalScale (ε : ℝ) : ℝ × E →L[ℝ] CKTimeSpace E :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (((ε ^ 2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ E).prod
      (ε⁻¹ • ContinuousLinearMap.snd ℝ ℝ E))

@[simp] theorem ckInversePhysicalScale_apply (ε : ℝ) (z : ℝ × E) :
    ckInversePhysicalScale (E := E) ε z =
      WithLp.toLp 1 ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2) := rfl

theorem ckPhysicalScale_rightInverse (ε : ℝ) (hε : ε ≠ 0) (z : ℝ × E) :
    ckPhysicalScale (E := E) ε (ckInversePhysicalScale ε z) = z := by
  simp [ckPhysicalScale_apply, ckInversePhysicalScale_apply, smul_smul,
    ← mul_assoc, hε, pow_ne_zero 2 hε]

theorem ckPhysicalScale_leftInverse (ε : ℝ) (hε : ε ≠ 0) (z : CKTimeSpace E) :
    ckInversePhysicalScale (E := E) ε (ckPhysicalScale ε z) = z := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).injective
  simp [ckPhysicalScale_apply, ckInversePhysicalScale_apply, smul_smul,
    ← mul_assoc, hε, pow_ne_zero 2 hε]

/-- Germ equality after a nonzero anisotropic rescaling descends to the
physical germ through the explicit continuous inverse. -/
theorem ckGerm_eq_of_physicalScale {f g : ℝ × E → V}
    (ε : ℝ) (hε : ε ≠ 0)
    (h : f ∘ ckPhysicalScale ε =ᶠ[𝓝 0] g ∘ ckPhysicalScale ε) :
    f =ᶠ[𝓝 0] g := by
  have ht : Tendsto (ckInversePhysicalScale (E := E) ε) (𝓝 0) (𝓝 0) := by
    simpa using (ckInversePhysicalScale (E := E) ε).continuous.continuousAt.tendsto
  filter_upwards [ht.eventually h] with z hz
  simpa only [Function.comp_apply, ckPhysicalScale_rightInverse ε hε] using hz

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
  have hx := (hasFDerivAt_id z.2).const_smul ε⁻¹
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

/-- Symmetrization preserves the represented analytic germ. -/
theorem ckSymmetrize_hasFPowerSeriesAt {f : E → V}
    {p : FormalMultilinearSeries ℝ E V} {x : E}
    (hp : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt f (fun n => ckSymmetrize E V (p n)) x := by
  obtain ⟨r, hr⟩ := hp
  refine ⟨r, ⟨?_, hr.r_pos, ?_⟩⟩
  · exact hr.r_le.trans (FormalMultilinearSeries.radius_le_of_le
      (fun n => ckSymmetrize_norm_le E V (p n)))
  · intro y hy
    simpa only [ckSymmetrize_diagonal] using hr.hasSum hy

/-- The scalar absolute majorant tends to zero for a zero-constant series. -/
theorem ckMajorant_tendsto_zero (p : FormalMultilinearSeries ℝ E V)
    (hp₀ : p 0 = 0) {R : ℝ} (hR : 0 < R)
    (hs : Summable (fun n => ‖p n‖ * R ^ n)) :
    Tendsto (fun r : ℝ => ∑' n, ‖p n‖ * |r| ^ n) (𝓝 0) (𝓝 0) := by
  have hpoint (n : ℕ) :
      Tendsto (fun r : ℝ => ‖p n‖ * |r| ^ n) (𝓝 0) (𝓝 (0 : ℝ)) := by
    cases n with
    | zero => simpa [hp₀] using (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
    | succ n =>
      simpa using
        ((continuous_const.mul (continuous_abs.pow (n + 1))).continuousAt.tendsto :
          Tendsto (fun r : ℝ => ‖p (n + 1)‖ * |r| ^ (n + 1))
            (𝓝 0) (𝓝 (‖p (n + 1)‖ * |(0 : ℝ)| ^ (n + 1))))
  have habs : ∀ᶠ r : ℝ in 𝓝 0, |r| ≤ R :=
    (continuous_abs.continuousAt.tendsto).eventually
      (by simpa using eventually_le_nhds hR)
  have hbound : ∀ᶠ r : ℝ in 𝓝 0,
      ∀ n : ℕ, ‖‖p n‖ * |r| ^ n‖ ≤ ‖p n‖ * R ^ n := by
    filter_upwards [habs] with r hr n
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg r) hr n)
      (norm_nonneg _)
  simpa using tendsto_tsum_of_dominated_convergence hs hpoint hbound

/-- Every analytic zero germ admits a symmetric absolutely summable expansion
after every sufficiently small bounded linear change of variables. The norm
bound is strict, so two arbitrary analytic competitors enter a common ball. -/
theorem ckAnalytic_exists_small_comp_series {f : E → V}
    (hf : AnalyticAt ℝ f 0) (hf₀ : f 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Z →L[ℝ] E, ‖A‖ < δ →
      ∃ q : CKSeries Z V, ‖q‖ < 1 ∧ q.eval =ᶠ[𝓝 0] f ∘ A := by
  obtain ⟨p, hp⟩ := hf
  have hp₀ : p 0 = 0 := by
    ext v
    simpa [hf₀] using hp.coeff_zero v
  obtain ⟨r, hr⟩ := hp
  obtain ⟨R, hR₀, hR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast hR₀
  have hs : Summable (fun n => ‖p n‖ * (R : ℝ) ^ n) :=
    p.summable_norm_mul_pow (hR.trans_le hr.r_le)
  have hlim := ckMajorant_tendsto_zero p hp₀ hRpos hs
  obtain ⟨η, hη, hsmall⟩ := Metric.eventually_nhds_iff.mp
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨min η (R : ℝ), lt_min hη hRpos, ?_⟩
  intro A hA
  have hAR : ‖A‖ ≤ (R : ℝ) := (lt_of_lt_of_le hA (min_le_right _ _)).le
  let a : FormalMultilinearSeries ℝ Z V := p.compContinuousLinearMap A
  let b : FormalMultilinearSeries ℝ Z V := fun n => ckSymmetrize Z V (a n)
  have hb_le (n : ℕ) : ‖b n‖ ≤ ‖p n‖ * ‖A‖ ^ n :=
    (ckSymmetrize_norm_le Z V (a n)).trans (p.norm_compContinuousLinearMap_le A n)
  have hA_sum : Summable (fun n => ‖p n‖ * ‖A‖ ^ n) :=
    .of_nonneg_of_le (fun _ => by positivity)
      (fun n => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg A) hAR n) (norm_nonneg _)) hs
  have hb_sum : Summable (fun n => ‖b n‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hb_le hA_sum
  have ha : HasFPowerSeriesAt (f ∘ A) a 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa using (show HasFPowerSeriesAt f p 0 from ⟨r, hr⟩)
  have hb : HasFPowerSeriesAt (f ∘ A) b 0 := ckSymmetrize_hasFPowerSeriesAt ha
  have hb₀ : b 0 = 0 := by
    ext v
    simpa [Function.comp_apply, hf₀] using hb.coeff_zero v
  let q : CKSeries Z V := CKSeries.ofCoeffs b hb_sum hb₀
    (fun n v σ => ckSymmetrize_symmetric Z V (a n) v σ)
  refine ⟨q, ?_, ?_⟩
  · calc
      ‖q‖ = ∑' n, ‖b n‖ := q.norm_eq_tsum
      _ ≤ ∑' n, ‖p n‖ * ‖A‖ ^ n := tsum_le_tsum hb_le hb_sum hA_sum
      _ < 1 := by
        have hdist : dist ‖A‖ (0 : ℝ) < η := by
          simpa using lt_of_lt_of_le hA (min_le_left _ _)
        simpa using hsmall hdist
  · filter_upwards [hb.eventually_hasSum] with z hz
    simpa [CKSeries.eval, CKSeries.formal, q, zero_add] using hz.tsum_eq

theorem ckNormalizedSolution_small_timeSeries {g : CKRHS E V}
    {w : ℝ × E → V} (hw : CKNormalizedSolution g w) (hg₀ : g 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ q : CKSeries (CKTimeSpace E) V, ‖q‖ < 1 ∧
        q.eval =ᶠ[𝓝 0] ckTimeDerivative w ∘ ckPhysicalScale ε := by
  obtain ⟨δ, hδ, hseries⟩ := ckAnalytic_exists_small_comp_series
    (Z := CKTimeSpace E) (ckTimeDerivative_analyticAt hw.analytic)
    (ckNormalizedSolution_timeDerivative_zero hw hg₀)
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεδ
  apply hseries
  exact (ckPhysicalScale_norm_le ε hε.le
    (lt_of_lt_of_le hεδ (min_le_right _ _)).le).trans_lt
      (lt_of_lt_of_le hεδ (min_le_left _ _))

/-- Equality of coefficient representatives of the rescaled time derivatives
closes uniqueness of the original normalized analytic solutions. -/
theorem ckNormalizedSolution_eq_of_timeSeries {g : CKRHS E V}
    {w v : ℝ × E → V} (hw : CKNormalizedSolution g w)
    (hv : CKNormalizedSolution g v) (ε : ℝ) (hε : ε ≠ 0)
    (p q : CKSeries (CKTimeSpace E) V)
    (hp : p.eval =ᶠ[𝓝 0] ckTimeDerivative w ∘ ckPhysicalScale ε)
    (hq : q.eval =ᶠ[𝓝 0] ckTimeDerivative v ∘ ckPhysicalScale ε)
    (hpq : p = q) : w =ᶠ[𝓝 0] v := by
  subst q
  apply ckGerm_eq_of_timeDerivative_eq hw.analytic hv.analytic
  · exact Filter.EventuallyEq.trans hw.initial (Filter.EventuallyEq.symm hv.initial)
  · exact ckGerm_eq_of_physicalScale ε hε (hp.symm.trans hq)

/-- Reconstruction of a normalized analytic solution from an arbitrary
coefficient representative of its rescaled time derivative. -/
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

theorem ckInversePhysicalScale_unitBall_eventually (ε : ℝ) :
    ∀ᶠ z : ℝ × E in 𝓝 0, ‖ckInversePhysicalScale ε z‖ < 1 := by
  have ht := (ckInversePhysicalScale (E := E) ε).continuous.norm.continuousAt.tendsto
  exact ht.eventually (by simpa using eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))

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

theorem ckLocalSolution_iff_literature {n m : ℕ}
    (F : LiteratureCKRHS n m) (u₀ : LiteratureSpace n → LiteratureSpace m)
    (t₀ : ℝ) (x₀ : LiteratureSpace n) (u : ℝ × LiteratureSpace n → LiteratureSpace m) :
    CKLocalSolution F u₀ t₀ x₀ u ↔ LiteratureCKSolution F u₀ t₀ x₀ u := by
  constructor
  · intro h
    exact ⟨h.analytic, h.initial, h.equation⟩
  · intro h
    exact ⟨h.analytic, h.initial, h.equation⟩

/-- Exact affine transport and finite-dimensional specialization. -/
theorem literatureAnalyticCKInput_of_normalized
    (hnormalized : ∀ (n m : ℕ), 0 < n → 0 < m →
      ∀ (g : LiteratureCKRHS n m), AnalyticAt ℝ g 0 → g 0 = 0 →
        ∃ w : ℝ × LiteratureSpace n → LiteratureSpace m,
          CKNormalizedSolution g w ∧
            ∀ v : ℝ × LiteratureSpace n → LiteratureSpace m,
              CKNormalizedSolution g v → w =ᶠ[𝓝 0] v) :
    LiteratureAnalyticCKInput := by
  constructor
  intro n m hn hm F u₀ t₀ x₀ hu₀ hF
  have hF' : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀) := hF
  obtain ⟨u, hu, hu_unique⟩ := ckLocal_exists_unique_of_normalized
    (hnormalized n m hn hm) F u₀ t₀ x₀ hu₀ hF'
  refine ⟨u, (ckLocalSolution_iff_literature F u₀ t₀ x₀ u).mp hu, ?_⟩
  intro v hv
  exact hu_unique v ((ckLocalSolution_iff_literature F u₀ t₀ x₀ v).mpr hv)

/-- Exact LI01, obtained from native analytic coefficient convergence,
contraction, actual derivative identities, and arbitrary analytic-germ uniqueness. -/
theorem literatureAnalyticCKInput_native : LiteratureAnalyticCKInput :=
  literatureAnalyticCKInput_of_normalized
    (fun _n _m _hn _hm g hg hg₀ => ck_normalized_exists_unique g hg hg₀)

end

end NSEGR.NativeLiterature
