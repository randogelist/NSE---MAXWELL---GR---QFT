import GRAssembly.NativeGluingGaussianCoordinates
import GRAdapter.Contracts

/-! LI02 to a single periodic Gaussian collar, with actual Lorentzian witnesses. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

structure GaussianGluingLaw (K : BoundaryTensor) (t0 δ : ℝ)
    (f : GaussianJoint → BulkMatrix) (z : GaussianJoint) : Prop where
  time_mem : z.1.2 ∈ timeInterval t0 δ
  analytic : AnalyticAt ℝ (metricOfJoint f) (bulkFromJoint z)
  symmetric : (metricOfJoint f (bulkFromJoint z)).IsSymm
  nondegenerate : (metricOfJoint f (bulkFromJoint z)).det ≠ 0
  gaussian_rr : metricOfJoint f (bulkFromJoint z) 0 0 = 1
  gaussian_rboundary : ∀ a : Fin 4, metricOfJoint f (bulkFromJoint z) 0 (boundaryIndex a) = 0
  vacuum : ricci (metricOfJoint f) (bulkFromJoint z) = 0
  near_eta : ∀ a b : Fin 4,
    |metricOfJoint f (bulkFromJoint z) (boundaryIndex a) (boundaryIndex b) - eta4 a b| <
      (1 / 12 : ℝ)
  induced : z.1.1 = 0 → ∀ a b : Fin 4,
    metricOfJoint f (bulkPoint 0 z.1.2 z.2) (boundaryIndex a) (boundaryIndex b) = eta4 a b
  boundary_match : z.1.1 = 0 → boundaryK (metricOfJoint f) z.1.2 z.2 = K z.1.2 z.2

theorem GaussianGluingLaw.congr
    {K : BoundaryTensor} {t0 δ : ℝ} {f g : GaussianJoint → BulkMatrix} {z : GaussianJoint}
    (hf : GaussianGluingLaw K t0 δ f z) (he : f =ᶠ[𝓝 z] g) :
    GaussianGluingLaw K t0 δ g z := by
  have hm := metricOfJoint_germ he
  have hv := hm.self_of_nhds
  refine ⟨hf.time_mem, hf.analytic.congr hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hv] using hf.symmetric
  · simpa only [← hv] using hf.nondegenerate
  · simpa only [← hv] using hf.gaussian_rr
  · intro a
    rw [← hv]
    exact hf.gaussian_rboundary a
  · rw [← ricci_metric_germ hm]
    exact hf.vacuum
  · intro a b
    rw [← hv]
    exact hf.near_eta a b
  · intro hr a b
    have hp : bulkFromJoint z = bulkPoint 0 z.1.2 z.2 := by simp [hr]
    rw [← hp, ← hv, hp]
    exact hf.induced hr a b
  · intro hr
    have hp : bulkFromJoint z = bulkPoint 0 z.1.2 z.2 := by simp [hr]
    rw [← boundaryK_metric_germ (hp ▸ hm)]
    exact hf.boundary_match hr

theorem GaussianGluingLaw.translate
    {ρ t0 δ : ℝ} {K : BoundaryTensor} (hK : BoundaryAdmissible ρ t0 δ K)
    (f : GaussianJoint → BulkMatrix) (z : GaussianJoint) (n : Frequency)
    (hf : GaussianGluingLaw K t0 δ f (z.1, z.2 - integerSpatialShift n)) :
    GaussianGluingLaw K t0 δ (spatialTranslate f n) z := by
  have hp : bulkFromJoint z - bulkPoint 0 0 (integerSpatialShift n) =
      bulkFromJoint (z.1, z.2 - integerSpatialShift n) :=
    bulkPoint_sub_spatial _ _ _ _
  have ha : AnalyticAt ℝ (fun y => metricOfJoint f
      (y - bulkPoint 0 0 (integerSpatialShift n))) (bulkFromJoint z) := by
    apply hf.analytic.comp_of_eq (analyticAt_id.sub analyticAt_const)
    exact hp
  refine ⟨hf.time_mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [metricOfJoint_translate] using ha
  · simpa only [metricOfJoint_translate, hp] using hf.symmetric
  · simpa only [metricOfJoint_translate, hp] using hf.nondegenerate
  · simpa only [metricOfJoint_translate, hp] using hf.gaussian_rr
  · intro a
    simpa only [metricOfJoint_translate, hp] using hf.gaussian_rboundary a
  · simpa only [metricOfJoint_translate, ricci_comp_sub, hp] using hf.vacuum
  · intro a b
    simpa only [metricOfJoint_translate, hp] using hf.near_eta a b
  · intro hr a b
    simpa only [metricOfJoint_translate, bulkPoint_sub_spatial] using hf.induced hr a b
  · intro hr
    rw [metricOfJoint_translate, boundaryK_comp_spatial_sub, hf.boundary_match hr]
    exact spatialPeriodic_sub_integer (hK.periodic z.1.2 hf.time_mem) n z.2

theorem gaussianGluingLaw_germ_of_literature
    {ρ t0 δ : ℝ} {K : BoundaryTensor} {g : Metric} {x0 : Vec}
    (hK : BoundaryAdmissible ρ t0 δ K)
    (hg : LiteratureFlatGaussianGerm K t0 x0 g) :
    ∀ᶠ z in 𝓝 (((0 : ℝ), t0), x0), GaussianGluingLaw K t0 δ (jointMetric g) z := by
  have hp : Tendsto bulkFromJoint (𝓝 (((0 : ℝ), t0), x0))
      (𝓝 (bulkPoint 0 t0 x0)) := bulkFromJoint.continuous.tendsto _
  have hb : Tendsto (fun z : GaussianJoint => (z.1.2, z.2))
      (𝓝 (((0 : ℝ), t0), x0)) (𝓝 (t0, x0)) :=
    (continuous_fst.snd.prodMk continuous_snd).continuousAt.tendsto
  have ht : ∀ᶠ z : GaussianJoint in 𝓝 (((0 : ℝ), t0), x0),
      z.1.2 ∈ timeInterval t0 δ :=
    (continuous_fst.snd.continuousAt.tendsto).eventually
      (timeInterval_mem_nhds t0 δ hK.radius_pos)
  filter_upwards [ht, hp.eventually hg.analytic.eventually_analyticAt,
    hp.eventually hg.symmetric, hp.eventually hg.nondegenerate,
    hp.eventually hg.gaussian_rr, hp.eventually hg.gaussian_rboundary,
    hp.eventually hg.vacuum, hp.eventually (near_eta4_of_gaussianGerm hg),
    hb.eventually hg.induced, hb.eventually hg.boundary_match]
    with z ht ha hs hn hrr hrb hv hnear hi hm
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [metricOfJoint_jointMetric] using ha
  · simpa only [metricOfJoint_jointMetric] using hs
  · simpa only [metricOfJoint_jointMetric] using hn
  · simpa only [metricOfJoint_jointMetric] using hrr
  · simpa only [metricOfJoint_jointMetric] using hrb
  · simpa only [metricOfJoint_jointMetric] using hv
  · simpa only [metricOfJoint_jointMetric] using hnear
  · intro _
    simpa only [metricOfJoint_jointMetric] using hi
  · intro _
    simpa only [metricOfJoint_jointMetric] using hm

theorem literatureGaussianGerm_of_gluingLaw
    {K : BoundaryTensor} {t0 δ : ℝ} {f : GaussianJoint → BulkMatrix} {x0 : Vec}
    (hf : ∀ᶠ z in 𝓝 (((0 : ℝ), t0), x0), GaussianGluingLaw K t0 δ f z) :
    LiteratureFlatGaussianGerm K t0 x0 (metricOfJoint f) := by
  have hp : Tendsto jointFromBulk (𝓝 (bulkPoint 0 t0 x0))
      (𝓝 (((0 : ℝ), t0), x0)) := by simpa using jointFromBulk.continuous.tendsto (bulkPoint 0 t0 x0)
  have hb : Tendsto (fun z : ℝ × Vec => (((0 : ℝ), z.1), z.2))
      (𝓝 (t0, x0)) (𝓝 (((0 : ℝ), t0), x0)) :=
    ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousAt.tendsto
  refine ⟨hf.self_of_nhds.analytic, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hp.eventually hf] with z hz
    simpa only [bulkFromJoint_jointFromBulk] using hz.symmetric
  · filter_upwards [hp.eventually hf] with z hz
    simpa only [bulkFromJoint_jointFromBulk] using hz.nondegenerate
  · filter_upwards [hp.eventually hf] with z hz
    simpa only [bulkFromJoint_jointFromBulk] using hz.gaussian_rr
  · filter_upwards [hp.eventually hf] with z hz
    simpa only [bulkFromJoint_jointFromBulk] using hz.gaussian_rboundary
  · filter_upwards [hb.eventually hf] with z hz
    exact hz.induced rfl
  · filter_upwards [hb.eventually hf] with z hz
    exact hz.boundary_match rfl
  · filter_upwards [hp.eventually hf] with z hz
    simpa only [bulkFromJoint_jointFromBulk] using hz.vacuum

theorem lorentzian_of_gaussianGluingLaw
    {K : BoundaryTensor} {t0 δ : ℝ} {f : GaussianJoint → BulkMatrix} {z : GaussianJoint}
    (hf : GaussianGluingLaw K t0 δ f z) : LorentzianAt (metricOfJoint f) (bulkFromJoint z) := by
  let H : Tensor4 := fun a b => metricOfJoint f (bulkFromJoint z) a.succ b.succ
  have hs : ∀ a b, H a b = H b a := by
    intro a b
    exact congrArg (fun M : BulkMatrix => M b.succ a.succ) hf.symmetric
  obtain ⟨C, hC, hHC⟩ := lorentz_factor_of_near_eta4 H hs hf.near_eta
  have hm : metricOfJoint f (bulkFromJoint z) = gaussianMatrix H := by
    ext a b
    refine Fin.cases ?_ (fun i => ?_) a
    · refine Fin.cases ?_ (fun j => ?_) b
      · exact hf.gaussian_rr
      · exact hf.gaussian_rboundary j
    · refine Fin.cases ?_ (fun j => ?_) b
      · have he := congrArg (fun M : BulkMatrix => M 0 i.succ) hf.symmetric
        exact he.trans (hf.gaussian_rboundary i)
      · rfl
  have hLor := gaussianMetric_lorentzian_of_congruence
    (fun _ : Bulk => H) (bulkFromJoint z) C hC hHC
  rcases hLor with ⟨D, hD, he⟩
  exact ⟨D, hD, hm.trans he⟩

/-- One actual periodic Gaussian metric on a common radial/time collar. -/
theorem radialExtensionResult_of_literatureGaussian
    (input : LiteratureGaussianJetInput)
    {ρ t0 δ : ℝ} {K : BoundaryTensor} (hK : BoundaryAdmissible ρ t0 δ K) :
    Nonempty (RadialExtensionResult ρ t0 δ K) := by
  have hex (x : Vec) (_hx : x ∈ unitCube) :
      ∃ f : GaussianJoint → BulkMatrix,
        ∀ᶠ z in 𝓝 (((0 : ℝ), t0), x), GaussianGluingLaw K t0 δ f z := by
    obtain ⟨g, hg, _⟩ := input.exists_unique K t0 x
      (boundaryAdmissible_literatureFlatBoundaryGerm hK x)
    exact ⟨jointMetric g, gaussianGluingLaw_germ_of_literature hK hg⟩
  have hlocality (f g : GaussianJoint → BulkMatrix) (z : GaussianJoint)
      (he : f =ᶠ[𝓝 z] g) : GaussianGluingLaw K t0 δ f z ↔ GaussianGluingLaw K t0 δ g z :=
    ⟨fun hf => hf.congr he, fun hg => hg.congr he.symm⟩
  have huniq (f g : GaussianJoint → BulkMatrix) (x : Vec)
      (hf : ∀ᶠ z in 𝓝 (((0 : ℝ), t0), x), GaussianGluingLaw K t0 δ f z)
      (hg : ∀ᶠ z in 𝓝 (((0 : ℝ), t0), x), GaussianGluingLaw K t0 δ g z) :
      f =ᶠ[𝓝 (((0 : ℝ), t0), x)] g := by
    have he := literatureGaussianJet_unique input
      (boundaryAdmissible_literatureFlatBoundaryGerm hK x)
      (literatureGaussianGerm_of_gluingLaw hf) (literatureGaussianGerm_of_gluingLaw hg)
    simpa only [jointMetric_metricOfJoint] using jointMetric_germ he
  obtain ⟨W, hW, hsW, f, hper, hlaw⟩ :=
    periodic_law_of_unique_local_germs (GaussianGluingLaw K t0 δ)
      hex hlocality (GaussianGluingLaw.translate hK) huniq eta5
  obtain ⟨R, T, hR, h0R, hT, htT, hRT⟩ := GRTemp.ML001.endpoint.mp (hW.mem_nhds hsW)
  obtain ⟨e, he, _, heR⟩ := positive_timeInterval_subset (show (0 : ℝ) < 1 by norm_num)
    (hR.mem_nhds h0R)
  obtain ⟨d, hd, hdδ, hdT⟩ := positive_timeInterval_subset hK.radius_pos (hT.mem_nhds htT)
  have hcollar {z : Bulk} (hz : z ∈ bulkCollar t0 d e) :
      GaussianGluingLaw K t0 δ f (jointFromBulk z) := by
    apply hlaw
    exact hRT ⟨heR (by simpa [timeInterval] using hz.1), hdT hz.2⟩
  have hpoint (r : ℝ) (hr : r ∈ Ioo (-e) e) (t : ℝ) (ht : t ∈ timeInterval t0 d) (x : Vec) :
      GaussianGluingLaw K t0 δ f ((r, t), x) :=
    hlaw (r, t) (hRT ⟨heR (by simpa [timeInterval] using hr), hdT ht⟩) x
  have hmatch : ∀ t ∈ timeInterval t0 d, boundaryK (metricOfJoint f) t = K t := by
    intro t ht
    funext x
    exact (hpoint 0 (by constructor <;> linarith) t ht x).boundary_match rfl
  have hbeta : ∀ x, (fun t => boundaryBeta (boundaryK (metricOfJoint f)) t x)
      =ᶠ[𝓝 t0] (fun t => boundaryBeta K t x) := by
    intro x
    filter_upwards [timeInterval_mem_nhds t0 d hd] with t ht
    exact congrFun (boundaryBeta_congr_slice _ _ t (hmatch t ht)) x
  refine ⟨{ timeRadius := d, time_radius_le := hdδ, radialRadius := e,
    metric := metricOfJoint f, boundary_match := hmatch, geometry := ?_ }⟩
  refine ⟨hd, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [bulkFromJoint_jointFromBulk] using (hcollar hz).analytic
  · intro r hr t ht
    simpa only [metricOfJoint, jointFromBulk_apply, bulkPoint_radial, bulkPoint_time,
      bulkSpatialCoordinates_bulkPoint] using
      hper (r, t) (hRT ⟨heR (by simpa [timeInterval] using hr), hdT ht⟩)
  · intro z hz
    simpa only [bulkFromJoint_jointFromBulk] using (hcollar hz).symmetric
  · intro z hz
    simpa only [bulkFromJoint_jointFromBulk] using lorentzian_of_gaussianGluingLaw (hcollar hz)
  · intro z hz
    simpa only [bulkFromJoint_jointFromBulk] using (hcollar hz).gaussian_rr
  · intro z hz
    simpa only [bulkFromJoint_jointFromBulk] using (hcollar hz).gaussian_rboundary
  · intro t ht x a b
    exact (hpoint 0 (by constructor <;> linarith) t ht x).induced rfl a b
  · intro z hz
    simpa only [bulkFromJoint_jointFromBulk] using (hcollar hz).vacuum
  · intro x
    exact (hbeta x).self_of_nhds.trans (hK.beta_initial x)
  · intro x
    rw [(hbeta x).deriv_eq]
    exact hK.beta_time_initial x

/-- The exact native radial contract; LI02 is the only unresolved input. -/
theorem analyticRadialExtensionLaws_of_literatureGaussian
    (input : LiteratureGaussianJetInput) (ρ t0 : ℝ) : AnalyticRadialExtensionLaws ρ t0 where
  extend := fun _ _ hK => radialExtensionResult_of_literatureGaussian input hK

end
end NSEGR.Assembly
