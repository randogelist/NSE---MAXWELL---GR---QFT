import GRAssembly.NativeGluingTranslation
import GRAdapter.Locality
import GRAssembly.LorentzNeighborhood

/-! Exact coordinate transport and germ locality for the Gaussian atlas. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

abbrev GaussianJoint := (ℝ × ℝ) × Vec

def bulkFromJoint : GaussianJoint →L[ℝ] Bulk :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => bulkPoint z.1.1 z.1.2 z.2
      map_add' := by
        intro a b
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
      map_smul' := by
        intro a b
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl }

def jointFromBulk : Bulk →L[ℝ] GaussianJoint :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ((z 0, z 1), bulkSpatialCoordinates z)
      map_add' := by
        intro a b
        apply Prod.ext
        · rfl
        · ext i; rfl
      map_smul' := by
        intro a b
        apply Prod.ext
        · rfl
        · ext i; rfl }

@[simp] theorem bulkFromJoint_apply (z : GaussianJoint) :
    bulkFromJoint z = bulkPoint z.1.1 z.1.2 z.2 := rfl

@[simp] theorem jointFromBulk_apply (z : Bulk) :
    jointFromBulk z = ((z 0, z 1), bulkSpatialCoordinates z) := rfl

@[simp] theorem bulkSpatialCoordinates_bulkPoint (r t : ℝ) (x : Vec) :
    bulkSpatialCoordinates (bulkPoint r t x) = x := by ext i; rfl

@[simp] theorem jointFromBulk_bulkFromJoint (z : GaussianJoint) :
    jointFromBulk (bulkFromJoint z) = z := by
  simp only [bulkFromJoint_apply, jointFromBulk_apply, bulkPoint_radial,
    bulkPoint_time, bulkSpatialCoordinates_bulkPoint, Prod.mk.eta]

@[simp] theorem bulkFromJoint_jointFromBulk (z : Bulk) :
    bulkFromJoint (jointFromBulk z) = z := bulkPoint_coordinates z

def jointMetric (g : Metric) : GaussianJoint → BulkMatrix := fun z => g (bulkFromJoint z)

def metricOfJoint (f : GaussianJoint → BulkMatrix) : Metric := fun z => f (jointFromBulk z)

@[simp] theorem jointMetric_metricOfJoint (f : GaussianJoint → BulkMatrix) :
    jointMetric (metricOfJoint f) = f := by
  funext z
  simp only [jointMetric, metricOfJoint, jointFromBulk_bulkFromJoint]

@[simp] theorem metricOfJoint_jointMetric (g : Metric) :
    metricOfJoint (jointMetric g) = g := by
  funext z
  simp only [jointMetric, metricOfJoint, bulkFromJoint_jointFromBulk]

theorem metricOfJoint_germ {f g : GaussianJoint → BulkMatrix} {z : GaussianJoint}
    (h : f =ᶠ[𝓝 z] g) : metricOfJoint f =ᶠ[𝓝 (bulkFromJoint z)] metricOfJoint g := by
  exact h.comp_tendsto (by simpa using jointFromBulk.continuous.tendsto (bulkFromJoint z))

theorem jointMetric_germ {g h : Metric} {z : GaussianJoint}
    (he : g =ᶠ[𝓝 (bulkFromJoint z)] h) : jointMetric g =ᶠ[𝓝 z] jointMetric h :=
  he.comp_tendsto bulkFromJoint.continuous.continuousAt.tendsto

theorem metricOfJoint_translate (f : GaussianJoint → BulkMatrix) (n : Frequency) :
    metricOfJoint (spatialTranslate f n) =
      fun z => metricOfJoint f (z - bulkPoint 0 0 (integerSpatialShift n)) := by
  funext z
  change f ((z 0, z 1), bulkSpatialCoordinates z - integerSpatialShift n) =
    f (((z - bulkPoint 0 0 (integerSpatialShift n)) 0,
      (z - bulkPoint 0 0 (integerSpatialShift n)) 1),
      bulkSpatialCoordinates (z - bulkPoint 0 0 (integerSpatialShift n)))
  congr 1
  apply Prod.ext
  · simp [bulkPoint]
  · ext i; rfl

theorem bulkPartial_metric_germ {g h : Metric} {z : Bulk}
    (he : g =ᶠ[𝓝 z] h) (a b i : Fin 5) :
    bulkPartial (fun y => g y a b) i z = bulkPartial (fun y => h y a b) i z := by
  have hc : (fun y => g y a b) =ᶠ[𝓝 z] (fun y => h y a b) :=
    he.mono (fun _ hy => congrArg (fun M : BulkMatrix => M a b) hy)
  unfold bulkPartial
  rw [hc.fderiv_eq]

theorem christoffel_metric_germ {g h : Metric} {z : Bulk}
    (he : g =ᶠ[𝓝 z] h) (a b c : Fin 5) :
    christoffel g z a b c = christoffel h z a b c := by
  unfold christoffel inverseMetric
  rw [he.self_of_nhds]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [bulkPartial_metric_germ he, bulkPartial_metric_germ he, bulkPartial_metric_germ he]

theorem ricci_metric_germ {g h : Metric} {z : Bulk}
    (he : g =ᶠ[𝓝 z] h) : ricci g z = ricci h z := by
  have hΓ (a b c : Fin 5) : (fun y => christoffel g y a b c) =ᶠ[𝓝 z]
      (fun y => christoffel h y a b c) :=
    he.eventuallyEq_nhds.mono (fun _ hy => christoffel_metric_germ hy a b c)
  have hd (a b c i : Fin 5) :
      bulkPartial (fun y => christoffel g y a b c) i z =
      bulkPartial (fun y => christoffel h y a b c) i z := by
    unfold bulkPartial
    rw [(hΓ a b c).fderiv_eq]
  ext a b
  simp only [ricci, hd, christoffel_metric_germ he]

theorem boundaryK_metric_germ {g h : Metric} {t : ℝ} {x : Vec}
    (he : g =ᶠ[𝓝 (bulkPoint 0 t x)] h) : boundaryK g t x = boundaryK h t x := by
  ext a b
  unfold boundaryK
  rw [bulkPartial_metric_germ he]

def gluingMetricEntry (a b : Fin 5) : BulkMatrix →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M a b
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem near_eta4_of_gaussianGerm {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {g : Metric} (hg : LiteratureFlatGaussianGerm K t0 x0 g) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), ∀ a b : Fin 4,
      |g z (boundaryIndex a) (boundaryIndex b) - eta4 a b| < (1 / 12 : ℝ) := by
  apply Filter.eventually_all.mpr
  intro a
  apply Filter.eventually_all.mpr
  intro b
  have hc : ContinuousAt
      (fun z : Bulk => |g z (boundaryIndex a) (boundaryIndex b) - eta4 a b|)
      (bulkPoint 0 t0 x0) :=
    (((gluingMetricEntry (boundaryIndex a) (boundaryIndex b)).continuous.continuousAt.comp
      hg.analytic.continuousAt).sub continuousAt_const).abs
  have hzero := hg.induced.self_of_nhds a b
  apply hc.eventually
  apply gt_mem_nhds
  rw [hzero]
  norm_num

end
end NSEGR.Assembly
