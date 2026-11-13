import GRAdapter.LiteratureInputs
import Mathlib.Analysis.Calculus.MeanValue

/-!
Affine normalization of the literal finite-dimensional analytic CK problem.
All operators are actual derivatives. No CK existence theorem is assumed.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.NativeLiterature

noncomputable section

variable {E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

abbrev CKJet (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  (ℝ × E) × (V × (E →L[ℝ] V))

abbrev CKRHS (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] := CKJet E V → V

def ckInitialJet (t₀ : ℝ) (x₀ : E) (u₀ : E → V) : CKJet E V :=
  ((t₀, x₀), (u₀ x₀, fderiv ℝ u₀ x₀))

structure CKLocalSolution (F : CKRHS E V) (u₀ : E → V)
    (t₀ : ℝ) (x₀ : E) (u : ℝ × E → V) : Prop where
  analytic : AnalyticAt ℝ u (t₀, x₀)
  initial : ∀ᶠ x in 𝓝 x₀, u (t₀, x) = u₀ x
  equation : ∀ᶠ z in 𝓝 (t₀, x₀),
    deriv (fun t : ℝ => u (t, z.2)) z.1 =
      F (z, (u z, fderiv ℝ (fun x => u (z.1, x)) z.2))

def ckInitialVelocity (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) : V :=
  F (ckInitialJet t₀ x₀ u₀)

def ckNormalizeJet (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (J : CKJet E V) : CKJet E V :=
  ((t₀ + J.1.1, x₀ + J.1.2),
    (u₀ (x₀ + J.1.2) + J.1.1 • ckInitialVelocity F u₀ t₀ x₀ + J.2.1,
      fderiv ℝ u₀ (x₀ + J.1.2) + J.2.2))

def ckNormalizeRHS (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) : CKRHS E V :=
  fun J => F (ckNormalizeJet F u₀ t₀ x₀ J) - ckInitialVelocity F u₀ t₀ x₀

def ckNormalizeSolution (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (u : ℝ × E → V) :
    ℝ × E → V :=
  fun z => u (t₀ + z.1, x₀ + z.2) - u₀ (x₀ + z.2) -
    z.1 • ckInitialVelocity F u₀ t₀ x₀

def ckDenormalizeSolution (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (w : ℝ × E → V) :
    ℝ × E → V :=
  fun z => u₀ z.2 + (z.1 - t₀) • ckInitialVelocity F u₀ t₀ x₀ +
    w (z.1 - t₀, z.2 - x₀)

abbrev CKNormalizedSolution (g : CKRHS E V)
    (w : ℝ × E → V) : Prop :=
  CKLocalSolution g (fun _ => 0) 0 0 w

def ckTimeDerivative (w : ℝ × E → V) (z : ℝ × E) : V :=
  deriv (fun t => w (t, z.2)) z.1

def ckSpaceDerivative (w : ℝ × E → V) (z : ℝ × E) : E →L[ℝ] V :=
  fderiv ℝ (fun x => w (z.1, x)) z.2

theorem ckSpaceDerivative_eq_fderiv {w : ℝ × E → V} {z : ℝ × E}
    (hw : DifferentiableAt ℝ w z) :
    ckSpaceDerivative w z =
      (fderiv ℝ w z).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hpath := (hasFDerivAt_const z.2 z.1).prodMk (hasFDerivAt_id z.2)
  simpa only [ckSpaceDerivative, Function.comp_def, id_eq, Prod.eta] using
    (hw.hasFDerivAt.comp z.2 hpath).fderiv

theorem ckSpaceDerivative_germ_of_eq {w v : ℝ × E → V}
    (hw : AnalyticAt ℝ w 0) (hv : AnalyticAt ℝ v 0)
    (h : w =ᶠ[𝓝 0] v) : ckSpaceDerivative w =ᶠ[𝓝 0] ckSpaceDerivative v := by
  filter_upwards [hw.eventually_analyticAt, hv.eventually_analyticAt,
    Filter.EventuallyEq.fderiv (𝕜 := ℝ) h] with z hzw hzv hz
  rw [ckSpaceDerivative_eq_fderiv hzw.differentiableAt,
    ckSpaceDerivative_eq_fderiv hzv.differentiableAt, hz]

def ckScaledSolution (ε : ℝ) (w : ℝ × E → V) (z : ℝ × E) : V :=
  w (ε ^ 2 * z.1, ε • z.2)

theorem ckScaledSolution_analyticAt {w : ℝ × E → V}
    (hw : AnalyticAt ℝ w 0) (ε : ℝ) : AnalyticAt ℝ (ckScaledSolution ε w) 0 := by
  have ht : AnalyticAt ℝ (fun z : ℝ × E => ε ^ 2 * z.1) 0 :=
    analyticAt_const.mul analyticAt_fst
  have hx : AnalyticAt ℝ (fun z : ℝ × E => ε • z.2) 0 :=
    analyticAt_const.smul analyticAt_snd
  exact hw.comp_of_eq (ht.prod hx) (by simp)

theorem ckScaledSolution_timeDerivative {w : ℝ × E → V} (ε : ℝ) (z : ℝ × E)
    (hw : DifferentiableAt ℝ (fun t => w (t, ε • z.2)) (ε ^ 2 * z.1)) :
    ckTimeDerivative (ckScaledSolution ε w) z =
      ε ^ 2 • ckTimeDerivative w (ε ^ 2 * z.1, ε • z.2) := by
  have ht := hw.hasDerivAt.scomp z.1 ((hasDerivAt_id z.1).const_mul (ε ^ 2))
  simpa only [ckTimeDerivative, ckScaledSolution, Function.comp_def, id_eq, mul_one] using
    ht.deriv

theorem ckScaledSolution_spaceDerivative {w : ℝ × E → V} (ε : ℝ) (z : ℝ × E)
    (hw : DifferentiableAt ℝ (fun x => w (ε ^ 2 * z.1, x)) (ε • z.2)) :
    ckSpaceDerivative (ckScaledSolution ε w) z =
      (ckSpaceDerivative w (ε ^ 2 * z.1, ε • z.2)).comp
        (ε • ContinuousLinearMap.id ℝ E) := by
  have hx := (hasFDerivAt_id z.2).const_smul ε
  simpa only [ckSpaceDerivative, ckScaledSolution, Function.comp_def, id_eq] using
    (hw.hasFDerivAt.comp z.2 hx).fderiv

theorem ckTimeDerivative_eq_fderiv {w : ℝ × E → V} {z : ℝ × E}
    (hw : DifferentiableAt ℝ w z) :
    ckTimeDerivative w z = fderiv ℝ w z (1, 0) := by
  have hpath := (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  simpa only [ckTimeDerivative, Function.comp_def, id_eq, Prod.eta] using
    (hw.hasFDerivAt.comp_hasDerivAt z.1 hpath).deriv

theorem ckTimeDerivative_analyticAt {w : ℝ × E → V} {z : ℝ × E}
    (hw : AnalyticAt ℝ w z) : AnalyticAt ℝ (ckTimeDerivative w) z := by
  let L : ((ℝ × E) →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V (1, 0)
  have h : AnalyticAt ℝ (L ∘ fderiv ℝ w) z :=
    (L.analyticAt (fderiv ℝ w z)).comp hw.fderiv
  apply h.congr
  filter_upwards [hw.eventually_analyticAt] with y hy
  change fderiv ℝ w y (1, 0) = ckTimeDerivative w y
  exact (ckTimeDerivative_eq_fderiv hy.differentiableAt).symm

theorem ckTimeDerivative_germ_of_eq {w v : ℝ × E → V}
    (hw : AnalyticAt ℝ w 0) (hv : AnalyticAt ℝ v 0)
    (h : w =ᶠ[𝓝 0] v) : ckTimeDerivative w =ᶠ[𝓝 0] ckTimeDerivative v := by
  filter_upwards [hw.eventually_analyticAt, hv.eventually_analyticAt,
    Filter.EventuallyEq.fderiv (𝕜 := ℝ) h] with z hzw hzv hz
  rw [ckTimeDerivative_eq_fderiv hzw.differentiableAt,
    ckTimeDerivative_eq_fderiv hzv.differentiableAt, hz]

theorem ckNormalizedSolution_congr {g : CKRHS E V} {w v : ℝ × E → V}
    (hw : CKNormalizedSolution g w) (h : w =ᶠ[𝓝 0] v) :
    CKNormalizedSolution g v := by
  have hv := hw.analytic.congr h
  refine ⟨hv, ?_, ?_⟩
  · have ht : Tendsto (fun x : E => ((0 : ℝ), x)) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_const.prodMk continuous_id).continuousAt.tendsto :
        Tendsto (fun x : E => ((0 : ℝ), x)) (𝓝 0) (𝓝 ((0 : ℝ), (0 : E))))
    filter_upwards [ht.eventually h, hw.initial] with x hx hx₀
    exact hx.symm.trans hx₀
  · filter_upwards [hw.equation, h, ckTimeDerivative_germ_of_eq hw.analytic hv h,
      ckSpaceDerivative_germ_of_eq hw.analytic hv h] with z heq hz ht hx
    change ckTimeDerivative v z = g (z, (v z, ckSpaceDerivative v z))
    rw [← ht, ← hx, ← hz]
    exact heq

theorem ckNormalizedSolution_timeDerivative_zero {g : CKRHS E V}
    {w : ℝ × E → V} (hw : CKNormalizedSolution g w) (hg₀ : g 0 = 0) :
    ckTimeDerivative w 0 = 0 := by
  have hw₀ : w (0, 0) = 0 :=
    Filter.Eventually.self_of_nhds (p := fun x : E => w (0, x) = 0) hw.initial
  have hdx : fderiv ℝ (fun x => w (0, x)) 0 = 0 := by
    simpa using Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hw.initial
  have heq := Filter.Eventually.self_of_nhds hw.equation
  change g (((0 : ℝ), (0 : E)), ((0 : V), (0 : E →L[ℝ] V))) = 0 at hg₀
  simpa [ckTimeDerivative, hw₀, hdx, hg₀] using heq

/-- Equality of analytic time derivatives and initial germs determines the
whole germ. This is the one-dimensional mean-value theorem on a common rectangle. -/
theorem ckGerm_eq_of_timeDerivative_eq {w v : ℝ × E → V}
    (hw : AnalyticAt ℝ w 0) (hv : AnalyticAt ℝ v 0)
    (hinitial : ∀ᶠ x in 𝓝 (0 : E), w (0, x) = v (0, x))
    (hderiv : ckTimeDerivative w =ᶠ[𝓝 0] ckTimeDerivative v) :
    w =ᶠ[𝓝 0] v := by
  have hp : ∀ᶠ z in 𝓝 (0 : ℝ × E),
      AnalyticAt ℝ w z ∧ AnalyticAt ℝ v z ∧
        ckTimeDerivative w z = ckTimeDerivative v z :=
    hw.eventually_analyticAt.and (hv.eventually_analyticAt.and hderiv)
  have hp' : ∀ᶠ z in 𝓝 (0 : ℝ) ×ˢ 𝓝 (0 : E),
      AnalyticAt ℝ w z ∧ AnalyticAt ℝ v z ∧
        ckTimeDerivative w z = ckTimeDerivative v z := by
    change ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : E)),
      AnalyticAt ℝ w z ∧ AnalyticAt ℝ v z ∧
        ckTimeDerivative w z = ckTimeDerivative v z at hp
    simpa only [nhds_prod_eq] using hp
  obtain ⟨ε, hε, p, hpx, hrect⟩ := Metric.eventually_nhds_prod_iff.mp hp'
  change ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : E)), w z = v z
  rw [nhds_prod_eq]
  apply Metric.eventually_nhds_prod_iff.mpr
  refine ⟨ε, hε, (fun x => p x ∧ w (0, x) = v (0, x)), hpx.and hinitial, ?_⟩
  intro t ht x hx
  have hwd : DifferentiableOn ℝ (fun s : ℝ => w (s, x)) (Metric.ball 0 ε) := by
    intro s hs
    exact (hrect hs hx.1).1.curry_left.differentiableAt.differentiableWithinAt
  have hvd : DifferentiableOn ℝ (fun s : ℝ => v (s, x)) (Metric.ball 0 ε) := by
    intro s hs
    exact (hrect hs hx.1).2.1.curry_left.differentiableAt.differentiableWithinAt
  have hdeq : (Metric.ball (0 : ℝ) ε).EqOn
      (deriv (fun s => w (s, x))) (deriv (fun s => v (s, x))) := by
    intro s hs
    exact (hrect hs hx.1).2.2
  exact (Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℝ) ε).isPreconnected
    hwd hvd hdeq (by simpa using hε) hx.2) ht

@[simp] theorem ckNormalizeJet_zero (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) :
    ckNormalizeJet F u₀ t₀ x₀ 0 = ckInitialJet t₀ x₀ u₀ := by
  simp [ckNormalizeJet, ckInitialJet]

@[simp] theorem ckNormalizeRHS_zero (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) : ckNormalizeRHS F u₀ t₀ x₀ 0 = 0 := by
  simp [ckNormalizeRHS, ckInitialVelocity]

theorem ckNormalizeJet_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (hu₀ : AnalyticAt ℝ u₀ x₀) :
    AnalyticAt ℝ (ckNormalizeJet F u₀ t₀ x₀) 0 := by
  have ht : AnalyticAt ℝ (fun J : CKJet E V => J.1.1) 0 :=
    analyticAt_fst.comp analyticAt_fst
  have hx : AnalyticAt ℝ (fun J : CKJet E V => J.1.2) 0 :=
    analyticAt_snd.comp analyticAt_fst
  have hy : AnalyticAt ℝ (fun J : CKJet E V => J.2.1) 0 :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℝ (fun J : CKJet E V => J.2.2) 0 :=
    analyticAt_snd.comp analyticAt_snd
  have hxs : AnalyticAt ℝ (fun J : CKJet E V => x₀ + J.1.2) 0 :=
    analyticAt_const.add hx
  have hu : AnalyticAt ℝ (fun J : CKJet E V => u₀ (x₀ + J.1.2)) 0 :=
    hu₀.comp_of_eq hxs (by simp)
  have hdu : AnalyticAt ℝ
      (fun J : CKJet E V => fderiv ℝ u₀ (x₀ + J.1.2)) 0 :=
    hu₀.fderiv.comp_of_eq hxs (by simp)
  exact ((analyticAt_const.add ht).prod hxs).prod
    (((hu.add (ht.smul analyticAt_const)).add hy).prod (hdu.add hz))

theorem ckNormalizeRHS_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (hu₀ : AnalyticAt ℝ u₀ x₀)
    (hF : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀)) :
    AnalyticAt ℝ (ckNormalizeRHS F u₀ t₀ x₀) 0 := by
  have hF' : AnalyticAt ℝ F (ckNormalizeJet F u₀ t₀ x₀ 0) := by
    simpa using hF
  exact (hF'.comp (ckNormalizeJet_analyticAt F u₀ t₀ x₀ hu₀)).sub analyticAt_const

@[simp] theorem ckDenormalize_normalize (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (u : ℝ × E → V) :
    ckDenormalizeSolution F u₀ t₀ x₀ (ckNormalizeSolution F u₀ t₀ x₀ u) = u := by
  funext z
  simp only [ckDenormalizeSolution, ckNormalizeSolution, add_sub_cancel,
    sub_add_cancel, add_sub_cancel_left]
  abel

@[simp] theorem ckNormalize_denormalize (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (w : ℝ × E → V) :
    ckNormalizeSolution F u₀ t₀ x₀ (ckDenormalizeSolution F u₀ t₀ x₀ w) = w := by
  funext z
  simp only [ckNormalizeSolution, ckDenormalizeSolution, add_sub_cancel_left]
  abel

theorem ckNormalizeSolution_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {u : ℝ × E → V}
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu : AnalyticAt ℝ u (t₀, x₀)) :
    AnalyticAt ℝ (ckNormalizeSolution F u₀ t₀ x₀ u) 0 := by
  have hxs : AnalyticAt ℝ (fun z : ℝ × E => x₀ + z.2) 0 :=
    analyticAt_const.add analyticAt_snd
  have hts : AnalyticAt ℝ (fun z : ℝ × E => t₀ + z.1) 0 :=
    analyticAt_const.add analyticAt_fst
  have hua : AnalyticAt ℝ (fun z : ℝ × E =>
      u (t₀ + z.1, x₀ + z.2)) 0 :=
    hu.comp_of_eq (hts.prod hxs) (by simp)
  have hu₀a : AnalyticAt ℝ (fun z : ℝ × E => u₀ (x₀ + z.2)) 0 :=
    hu₀.comp_of_eq hxs (by simp)
  exact (hua.sub hu₀a).sub (analyticAt_fst.smul analyticAt_const)

theorem ckDenormalizeSolution_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {w : ℝ × E → V}
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hw : AnalyticAt ℝ w 0) :
    AnalyticAt ℝ (ckDenormalizeSolution F u₀ t₀ x₀ w) (t₀, x₀) := by
  have hts : AnalyticAt ℝ (fun z : ℝ × E => z.1 - t₀) (t₀, x₀) :=
    analyticAt_fst.sub analyticAt_const
  have hxs : AnalyticAt ℝ (fun z : ℝ × E => z.2 - x₀) (t₀, x₀) :=
    analyticAt_snd.sub analyticAt_const
  have hwa : AnalyticAt ℝ (fun z : ℝ × E =>
      w (z.1 - t₀, z.2 - x₀)) (t₀, x₀) :=
    hw.comp_of_eq (hts.prod hxs) (by simp)
  exact ((hu₀.comp analyticAt_snd).add (hts.smul analyticAt_const)).add hwa

theorem ckNormalizeSolution_timeDerivative (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {u : ℝ × E → V}
    (z : ℝ × E)
    (hu : DifferentiableAt ℝ (fun t => u (t, x₀ + z.2)) (t₀ + z.1)) :
    deriv (fun t => ckNormalizeSolution F u₀ t₀ x₀ u (t, z.2)) z.1 =
      deriv (fun t => u (t, x₀ + z.2)) (t₀ + z.1) -
        ckInitialVelocity F u₀ t₀ x₀ := by
  have ht := hu.hasDerivAt.comp_const_add t₀ z.1
  have hc := (hasDerivAt_id z.1).smul_const (ckInitialVelocity F u₀ t₀ x₀)
  have hd : HasDerivAt
      (fun t => ckNormalizeSolution F u₀ t₀ x₀ u (t, z.2))
      (deriv (fun t => u (t, x₀ + z.2)) (t₀ + z.1) -
        (1 : ℝ) • ckInitialVelocity F u₀ t₀ x₀) z.1 :=
    ((ht.sub_const (u₀ (x₀ + z.2))).sub hc).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  simpa only [one_smul] using hd.deriv

theorem ckNormalizeSolution_spaceDerivative (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {u : ℝ × E → V}
    (z : ℝ × E)
    (hu : DifferentiableAt ℝ (fun x => u (t₀ + z.1, x)) (x₀ + z.2))
    (hu₀ : DifferentiableAt ℝ u₀ (x₀ + z.2)) :
    fderiv ℝ (fun x => ckNormalizeSolution F u₀ t₀ x₀ u (z.1, x)) z.2 =
      fderiv ℝ (fun x => u (t₀ + z.1, x)) (x₀ + z.2) -
        fderiv ℝ u₀ (x₀ + z.2) := by
  have hu' := (hasFDerivAt_comp_add_left x₀).mpr hu.hasFDerivAt
  have hu₀' := (hasFDerivAt_comp_add_left x₀).mpr hu₀.hasFDerivAt
  exact ((hu'.sub hu₀').sub_const (z.1 • ckInitialVelocity F u₀ t₀ x₀)).fderiv


theorem ckDenormalizeSolution_timeDerivative (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {w : ℝ × E → V}
    (z : ℝ × E)
    (hw : DifferentiableAt ℝ (fun t => w (t, z.2 - x₀)) (z.1 - t₀)) :
    deriv (fun t => ckDenormalizeSolution F u₀ t₀ x₀ w (t, z.2)) z.1 =
      ckInitialVelocity F u₀ t₀ x₀ +
        deriv (fun t => w (t, z.2 - x₀)) (z.1 - t₀) := by
  have ht := hw.hasDerivAt.comp_sub_const z.1 t₀
  have hc := ((hasDerivAt_id z.1).sub_const t₀).smul_const
    (ckInitialVelocity F u₀ t₀ x₀)
  have hd : HasDerivAt
      (fun t => ckDenormalizeSolution F u₀ t₀ x₀ w (t, z.2))
      (0 + (1 : ℝ) • ckInitialVelocity F u₀ t₀ x₀ +
        deriv (fun t => w (t, z.2 - x₀)) (z.1 - t₀)) z.1 :=
    (((hasDerivAt_const z.1 (u₀ z.2)).add hc).add ht).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  simpa only [one_smul, zero_add] using hd.deriv

theorem ckDenormalizeSolution_spaceDerivative (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {w : ℝ × E → V}
    (z : ℝ × E)
    (hw : DifferentiableAt ℝ (fun x => w (z.1 - t₀, x)) (z.2 - x₀))
    (hu₀ : DifferentiableAt ℝ u₀ z.2) :
    fderiv ℝ (fun x => ckDenormalizeSolution F u₀ t₀ x₀ w (z.1, x)) z.2 =
      fderiv ℝ u₀ z.2 + fderiv ℝ (fun x => w (z.1 - t₀, x)) (z.2 - x₀) := by
  have hw' := (hasFDerivAt_comp_sub x₀).mpr hw.hasFDerivAt
  exact ((hu₀.hasFDerivAt.add_const
    ((z.1 - t₀) • ckInitialVelocity F u₀ t₀ x₀)).add hw').fderiv

theorem ckNormalizeSolution_jet (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {u : ℝ × E → V}
    (z : ℝ × E)
    (hu : DifferentiableAt ℝ (fun x => u (t₀ + z.1, x)) (x₀ + z.2))
    (hu₀ : DifferentiableAt ℝ u₀ (x₀ + z.2)) :
    ckNormalizeJet F u₀ t₀ x₀
      (z, (ckNormalizeSolution F u₀ t₀ x₀ u z,
        fderiv ℝ (fun x => ckNormalizeSolution F u₀ t₀ x₀ u (z.1, x)) z.2)) =
      ((t₀ + z.1, x₀ + z.2),
        (u (t₀ + z.1, x₀ + z.2),
          fderiv ℝ (fun x => u (t₀ + z.1, x)) (x₀ + z.2))) := by
  rw [ckNormalizeSolution_spaceDerivative F u₀ t₀ x₀ z hu hu₀]
  dsimp only [ckNormalizeJet]
  refine Prod.ext ?_ ?_
  · rfl
  refine Prod.ext ?_ ?_
  · dsimp only [ckNormalizeJet, ckNormalizeSolution]
    abel
  · dsimp only [ckNormalizeJet]
    abel

theorem ckDenormalizeSolution_jet (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {w : ℝ × E → V}
    (z : ℝ × E)
    (hw : DifferentiableAt ℝ (fun x => w (z.1 - t₀, x)) (z.2 - x₀))
    (hu₀ : DifferentiableAt ℝ u₀ z.2) :
    ckNormalizeJet F u₀ t₀ x₀
      ((z.1 - t₀, z.2 - x₀),
        (w (z.1 - t₀, z.2 - x₀),
          fderiv ℝ (fun x => w (z.1 - t₀, x)) (z.2 - x₀))) =
      (z, (ckDenormalizeSolution F u₀ t₀ x₀ w z,
        fderiv ℝ (fun x => ckDenormalizeSolution F u₀ t₀ x₀ w (z.1, x)) z.2)) := by
  rw [ckDenormalizeSolution_spaceDerivative F u₀ t₀ x₀ z hw hu₀]
  have ht : t₀ + (z.1 - t₀) = z.1 := by abel
  have hx : x₀ + (z.2 - x₀) = z.2 := by abel
  simp only [ckNormalizeJet, ckDenormalizeSolution, ht, hx, Prod.eta]

theorem ckNormalizeSolution_isSolution (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {u : ℝ × E → V}
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu : CKLocalSolution F u₀ t₀ x₀ u) :
    CKNormalizedSolution (ckNormalizeRHS F u₀ t₀ x₀)
      (ckNormalizeSolution F u₀ t₀ x₀ u) := by
  have hshift : Tendsto (fun z : ℝ × E => (t₀ + z.1, x₀ + z.2))
      (𝓝 0) (𝓝 (t₀, x₀)) := by
    simpa using
      (((continuous_const.add continuous_fst).prodMk
        (continuous_const.add continuous_snd)).continuousAt.tendsto
        : Tendsto (fun z : ℝ × E => (t₀ + z.1, x₀ + z.2))
            (𝓝 0) (𝓝 (t₀ + (0 : ℝ × E).1, x₀ + (0 : ℝ × E).2)))
  have hxshift : Tendsto (fun x : E => x₀ + x) (𝓝 0) (𝓝 x₀) := by
    have hc : Continuous (fun x : E => x₀ + x) := by fun_prop
    simpa only [add_zero] using
      (hc.continuousAt.tendsto
        : Tendsto (fun x : E => x₀ + x) (𝓝 0) (𝓝 (x₀ + 0)))
  have hspace : Tendsto (fun z : ℝ × E => x₀ + z.2) (𝓝 0) (𝓝 x₀) := by
    have hc : Continuous (fun z : ℝ × E => x₀ + z.2) := by fun_prop
    simpa using
      (hc.continuousAt.tendsto
        : Tendsto (fun z : ℝ × E => x₀ + z.2) (𝓝 0) (𝓝 (x₀ + (0 : ℝ × E).2)))
  refine ⟨ckNormalizeSolution_analyticAt F u₀ t₀ x₀ hu₀ hu.analytic, ?_, ?_⟩
  · filter_upwards [hxshift.eventually hu.initial] with x hx
    simpa only [ckNormalizeSolution, zero_add, add_zero, zero_smul, sub_zero,
      sub_self] using congrArg (fun v => v - u₀ (x₀ + x)) hx
  · filter_upwards [hshift.eventually hu.equation,
      hshift.eventually hu.analytic.eventually_analyticAt,
      hspace.eventually hu₀.eventually_analyticAt] with z hz hzu hz₀
    rw [ckNormalizeSolution_timeDerivative F u₀ t₀ x₀ z
      hzu.curry_left.differentiableAt]
    change _ = F (ckNormalizeJet F u₀ t₀ x₀ _) - ckInitialVelocity F u₀ t₀ x₀
    rw [ckNormalizeSolution_jet F u₀ t₀ x₀ z
      hzu.curry_right.differentiableAt hz₀.differentiableAt]
    exact congrArg (fun v => v - ckInitialVelocity F u₀ t₀ x₀) hz

theorem ckDenormalizeSolution_isSolution (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {w : ℝ × E → V}
    (hu₀ : AnalyticAt ℝ u₀ x₀)
    (hw : CKNormalizedSolution (ckNormalizeRHS F u₀ t₀ x₀) w) :
    CKLocalSolution F u₀ t₀ x₀ (ckDenormalizeSolution F u₀ t₀ x₀ w) := by
  have hshift : Tendsto (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀))
      (𝓝 (t₀, x₀)) (𝓝 0) := by
    change Tendsto (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀))
      (𝓝 (t₀, x₀)) (𝓝 ((0 : ℝ), (0 : E)))
    have hc : Continuous (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀)) := by fun_prop
    simpa using
      (hc.continuousAt.tendsto
        : Tendsto (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀))
            (𝓝 (t₀, x₀)) (𝓝 (t₀ - t₀, x₀ - x₀)))
  have hxshift : Tendsto (fun x : E => x - x₀) (𝓝 x₀) (𝓝 0) := by
    have hc : Continuous (fun x : E => x - x₀) := by fun_prop
    simpa only [sub_self] using
      (hc.continuousAt.tendsto
        : Tendsto (fun x : E => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)))
  have hspace : Tendsto (fun z : ℝ × E => z.2) (𝓝 (t₀, x₀)) (𝓝 x₀) :=
    continuous_snd.continuousAt.tendsto
  refine ⟨ckDenormalizeSolution_analyticAt F u₀ t₀ x₀ hu₀ hw.analytic, ?_, ?_⟩
  · filter_upwards [hxshift.eventually hw.initial] with x hx
    simp only [ckDenormalizeSolution, sub_self, zero_smul, add_zero, hx]
  · filter_upwards [hshift.eventually hw.equation,
      hshift.eventually hw.analytic.eventually_analyticAt,
      hspace.eventually hu₀.eventually_analyticAt] with z hz hzw hz₀
    rw [ckDenormalizeSolution_timeDerivative F u₀ t₀ x₀ z
      hzw.curry_left.differentiableAt]
    change deriv (fun t => w (t, z.2 - x₀)) (z.1 - t₀) =
      F (ckNormalizeJet F u₀ t₀ x₀ _) - ckInitialVelocity F u₀ t₀ x₀ at hz
    rw [ckDenormalizeSolution_jet F u₀ t₀ x₀ z
      hzw.curry_right.differentiableAt hz₀.differentiableAt] at hz
    rw [hz]
    abel

theorem ckDenormalizeSolution_germ (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) {w v : ℝ × E → V}
    (h : w =ᶠ[𝓝 (0 : ℝ × E)] v) :
    ckDenormalizeSolution F u₀ t₀ x₀ w =ᶠ[𝓝 (t₀, x₀)]
      ckDenormalizeSolution F u₀ t₀ x₀ v := by
  have hshift : Tendsto (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀))
      (𝓝 (t₀, x₀)) (𝓝 0) := by
    change Tendsto (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀))
      (𝓝 (t₀, x₀)) (𝓝 ((0 : ℝ), (0 : E)))
    have hc : Continuous (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀)) := by fun_prop
    simpa using
      (hc.continuousAt.tendsto
        : Tendsto (fun z : ℝ × E => (z.1 - t₀, z.2 - x₀))
            (𝓝 (t₀, x₀)) (𝓝 (t₀ - t₀, x₀ - x₀)))
  filter_upwards [hshift.eventually h] with z hz
  exact congrArg (fun a => u₀ z.2 + (z.1 - t₀) • ckInitialVelocity F u₀ t₀ x₀ + a) hz

/-- Affine transport only; the normalized existence/uniqueness premise remains explicit. -/
theorem ckLocal_exists_unique_of_normalized
    (hnormalized : ∀ (g : CKRHS E V), AnalyticAt ℝ g 0 → g 0 = 0 →
      ∃ w : ℝ × E → V, CKNormalizedSolution g w ∧
        ∀ v : ℝ × E → V, CKNormalizedSolution g v → w =ᶠ[𝓝 0] v)
    (F : CKRHS E V) (u₀ : E → V) (t₀ : ℝ) (x₀ : E)
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hF : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀)) :
    ∃ u : ℝ × E → V, CKLocalSolution F u₀ t₀ x₀ u ∧
      ∀ v : ℝ × E → V, CKLocalSolution F u₀ t₀ x₀ v → u =ᶠ[𝓝 (t₀, x₀)] v := by
  obtain ⟨w, hw, huniq⟩ := hnormalized (ckNormalizeRHS F u₀ t₀ x₀)
    (ckNormalizeRHS_analyticAt F u₀ t₀ x₀ hu₀ hF) (ckNormalizeRHS_zero F u₀ t₀ x₀)
  refine ⟨ckDenormalizeSolution F u₀ t₀ x₀ w,
    ckDenormalizeSolution_isSolution F u₀ t₀ x₀ hu₀ hw, ?_⟩
  intro v hv
  have hnorm := ckNormalizeSolution_isSolution F u₀ t₀ x₀ hu₀ hv
  have he := ckDenormalizeSolution_germ F u₀ t₀ x₀ (huniq _ hnorm)
  simpa only [ckDenormalize_normalize] using he

end

end NSEGR.NativeLiterature
