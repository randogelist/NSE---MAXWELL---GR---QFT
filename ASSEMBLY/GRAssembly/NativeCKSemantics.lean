import GRAssembly.NativeCKGerm
import GRAssembly.NativeCKPrimitive

/-! Actual CK primitive semantics and physical analytic-solution reconstruction. -/

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
    have hpc : ContinuousAt p.eval (WithLp.toLp 1 (t, z.2)) :=
      (p.analyticAt ht).continuousAt
    exact hpc.comp (f := fun u : ℝ => WithLp.toLp 1 (u, z.2))
      (hc.continuousAt (x := t))
  have hseg : ∀ t ∈ Set.uIcc (0 : ℝ) z.1, t ∈ s := by
    intro t ht
    have habs : |t| ≤ |z.1| := by simpa using abs_sub_left_of_mem_uIcc ht
    have hz' : |z.1| + ‖z.2‖ < 1 := by
      simpa only [WithLp.prod_norm_eq_of_L1, WithLp.toLp_fst,
        WithLp.toLp_snd, Real.norm_eq_abs] using hz
    change ‖WithLp.toLp 1 (t, z.2)‖ < 1
    rw [WithLp.prod_norm_eq_of_L1]
    have ht' : |t| + ‖z.2‖ < 1 := by linarith
    simpa only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs] using
      ht'
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
  have hb : ∀ᶠ x in 𝓝 (0 : E), ‖x‖ < 1 := by
    have ht : Tendsto (norm : E → ℝ) (𝓝 0) (𝓝 0) := by
      simpa only [norm_zero] using (continuous_norm.continuousAt (x := (0 : E))).tendsto
    exact ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
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
    have hc : Continuous (fun x : E => ε⁻¹ • x) := by fun_prop
    simpa only [smul_zero] using (hc.continuousAt.tendsto :
      Tendsto (fun x : E => ε⁻¹ • x) (𝓝 0) (𝓝 (ε⁻¹ • (0 : E))))
  filter_upwards [ht.eventually (ckTimePrimitive_initial_germ p)] with x hx
  change ε ^ 2 • ckCoordinateEval (timePrimitive E V p)
    ((ε ^ 2)⁻¹ * 0, ε⁻¹ • x) = 0
  rw [mul_zero, hx, smul_zero]

theorem ckSeriesSolution_timeDerivative (ε : ℝ) (hε : ε ≠ 0)
    (p : CKSeries (CKTimeSpace E) V) {z : ℝ × E}
    (hz : ‖ckInversePhysicalScale ε z‖ < 1) :
    ckTimeDerivative (ckSeriesSolution ε p) z = p.eval (ckInversePhysicalScale ε z) := by
  have hpoint : ‖WithLp.toLp 1 ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)‖ < 1 := hz
  have hA := ckTimePrimitive_hasDerivAt p hpoint
  have hscaled := hA.scomp (h := fun t : ℝ => (ε ^ 2)⁻¹ * t) z.1
    (hasDerivAt_const_mul (x := z.1) ((ε ^ 2)⁻¹))
  have hfinal := hscaled.const_smul (ε ^ 2)
  have hphysical := hfinal.congr_of_eventuallyEq
    (f₁ := fun t : ℝ => ckSeriesSolution ε p (t, z.2))
    (Filter.Eventually.of_forall fun t => by rfl)
  simpa only [ckTimeDerivative, ckInversePhysicalScale_apply,
    ckCoordinateEval, id_eq, mul_one,
    smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hε), one_smul]
      using hphysical.deriv

theorem ckSeriesSolution_spaceDerivative (ε : ℝ)
    (p : CKSeries (CKTimeSpace E) V) {z : ℝ × E}
    (hz : ‖ckInversePhysicalScale ε z‖ < 1) :
    ckSpaceDerivative (ckSeriesSolution ε p) z =
      ε ^ 2 • (ckSpaceDerivative (ckCoordinateEval (timePrimitive E V p))
        ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ E) := by
  have hpoint : ‖WithLp.toLp 1 ((ε ^ 2)⁻¹ * z.1, ε⁻¹ • z.2)‖ < 1 := hz
  have hA := (ckCoordinateEval_analyticAt (timePrimitive E V p) hpoint).curry_right.differentiableAt
  have hx : HasFDerivAt (fun x : E => ε⁻¹ • x)
      (ε⁻¹ • ContinuousLinearMap.id ℝ E) z.2 := by
    simpa only [Pi.smul_def, id_eq] using
      (hasFDerivAt_id (𝕜 := ℝ) z.2).const_smul ε⁻¹
  have hscaled := hA.hasFDerivAt.comp (f := fun x : E => ε⁻¹ • x) z.2 hx
  have hfinal := hscaled.const_smul (ε ^ 2)
  have hphysical := hfinal.congr_of_eventuallyEq
    (f₁ := fun x : E => ckSeriesSolution ε p (z.1, x))
    (Filter.Eventually.of_forall fun x => by rfl)
  simpa only [ckSpaceDerivative] using hphysical.fderiv

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
      have hc : Continuous (fun x : E => ε • x) := by fun_prop
      simpa only [smul_zero] using (hc.continuousAt.tendsto :
        Tendsto (fun x : E => ε • x) (𝓝 0) (𝓝 (ε • (0 : E))))
    filter_upwards [hx.eventually hw.initial, ckTimePrimitive_initial_germ p] with x hx hAx
    simp only [ckScaledSolution, Pi.smul_apply, mul_zero, hx, hAx, smul_zero]
  · have hcoord : Tendsto (WithLp.toLp 1 : ℝ × E → CKTimeSpace E) (𝓝 0) (𝓝 0) := by
      have he : ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm :
          (ℝ × E) → CKTimeSpace E) = WithLp.toLp 1 := by
        funext z
        rfl
      simpa only [map_zero, he] using
        ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.continuous.continuousAt
          (x := (0 : ℝ × E))).tendsto
    have hscale : Tendsto (fun z : ℝ × E => (ε ^ 2 * z.1, ε • z.2)) (𝓝 0) (𝓝 0) := by
      have ht : Tendsto (ckPhysicalScale (E := E) ε) (𝓝 0) (𝓝 0) := by
        simpa only [map_zero] using
          ((ckPhysicalScale (E := E) ε).continuous.continuousAt (x := (0 : CKTimeSpace E))).tendsto
      exact ht.comp hcoord
    filter_upwards [hscale.eventually hw.analytic.eventually_analyticAt,
      hcoord.eventually hp, ckCoordinate_unitBall_eventually (E := E)] with z hzw hzp hz
    rw [ckScaledSolution_timeDerivative ε z hzw.curry_left.differentiableAt]
    have hAd := (ckTimePrimitive_hasDerivAt p hz).const_smul (ε ^ 2)
    have hAd' : deriv
        (fun t => ε ^ 2 • ckCoordinateEval (timePrimitive E V p) (t, z.2)) z.1 =
        ε ^ 2 • ckCoordinateEval p z := by
      simpa only [Pi.smul_def] using hAd.deriv
    change _ = deriv (fun t => ε ^ 2 • ckCoordinateEval (timePrimitive E V p) (t, z.2)) z.1
    rw [hAd']
    exact congrArg (fun v : V => ε ^ 2 • v) hzp.symm

theorem ckNormalizedSolution_eq_seriesSolution {g : CKRHS E V}
    {w : ℝ × E → V} (hw : CKNormalizedSolution g w) (ε : ℝ) (hε : ε ≠ 0)
    (p : CKSeries (CKTimeSpace E) V)
    (hp : p.eval =ᶠ[𝓝 0] ckTimeDerivative w ∘ ckPhysicalScale ε) :
    w =ᶠ[𝓝 0] ckSeriesSolution ε p := by
  have hrec := ckScaledSolution_eq_timePrimitive hw ε p hp
  have hcoord : Tendsto (WithLp.ofLp : CKTimeSpace E → ℝ × E) (𝓝 0) (𝓝 0) := by
    have he : (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E :
        CKTimeSpace E → ℝ × E) = WithLp.ofLp := by
      funext z
      rfl
    simpa only [map_zero, he] using
      ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).continuous.continuousAt
        (x := (0 : CKTimeSpace E))).tendsto
  apply ckGerm_eq_of_physicalScale ε hε
  filter_upwards [hcoord.eventually hrec] with z hz
  change w (ckPhysicalScale ε z) = ckSeriesSolution ε p (ckPhysicalScale ε z)
  rw [ckSeriesSolution, ckPhysicalScale_leftInverse ε hε]
  exact hz

end

end NSEGR.NativeLiterature
