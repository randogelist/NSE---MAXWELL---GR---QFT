import GRAssembly.BoundaryConstraintsGeometry
import GRAdapter.Sector

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 3200000

namespace NSEGR.Assembly
open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

def metricTangentialBlock (g : Metric) : Bulk → Tensor4 :=
  fun z a b => g z a.succ b.succ

theorem bulkCollar_isOpen (t0 δ ε : ℝ) : IsOpen (bulkCollar t0 δ ε) := by
  have h0 : Continuous (fun z : Bulk => z 0) := by fun_prop
  have h1 : Continuous (fun z : Bulk => z 1) := by fun_prop
  exact (isOpen_Ioo.preimage h0).inter (isOpen_Ioo.preimage h1)

theorem boundaryPoint_mem_collar {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ) (x : Vec) :
    bulkPoint 0 t x ∈ bulkCollar t0 δ ε := by
  exact ⟨⟨neg_lt_zero.mpr hg.radial_radius_pos, hg.radial_radius_pos⟩, ht⟩

theorem boundary_time_eventually {t0 δ t : ℝ} {x : Vec}
    (ht : t ∈ timeInterval t0 δ) :
    ∀ᶠ z : ℝ × Vec in 𝓝 (t, x), z.1 ∈ timeInterval t0 δ :=
  continuous_fst.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds ht)

theorem gaussianVacuum_block_analytic {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {z : Bulk} (hz : z ∈ bulkCollar t0 δ ε) :
    AnalyticAt ℝ (metricTangentialBlock g) z := by
  apply analyticAt_matrix_of_entries
  intro a b
  exact analyticAt_matrix_entry (hg.analytic z hz) a.succ b.succ

theorem gaussianVacuum_eq_gaussian {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {z : Bulk} (hz : z ∈ bulkCollar t0 δ ε) :
    g z = gaussianMetric (metricTangentialBlock g) z := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · exact hg.gaussian_rr z hz
    · exact hg.gaussian_rboundary z hz j
  · refine Fin.cases ?_ (fun j => ?_) b
    · exact ((hg.symmetric z hz).apply 0 i.succ).trans
        (hg.gaussian_rboundary z hz i)
    · rfl

theorem gaussianVacuum_eq_gaussian_germ {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {z : Bulk} (hz : z ∈ bulkCollar t0 δ ε) :
    g =ᶠ[𝓝 z] gaussianMetric (metricTangentialBlock g) := by
  filter_upwards [(bulkCollar_isOpen t0 δ ε).mem_nhds hz] with y hy
  exact gaussianVacuum_eq_gaussian hg hy

theorem gaussianVacuum_block_unit {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {z : Bulk} (hz : z ∈ bulkCollar t0 δ ε) :
    IsUnit (metricTangentialBlock g z).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [← gaussianMatrix_det]
  change (gaussianMetric (metricTangentialBlock g) z).det ≠ 0
  rw [← gaussianVacuum_eq_gaussian hg hz]
  exact gaussianVacuum_nondegenerate hg z hz

theorem gaussianVacuum_block_unit_germ {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {z : Bulk} (hz : z ∈ bulkCollar t0 δ ε) :
    ∀ᶠ y in 𝓝 z, IsUnit (metricTangentialBlock g y).det := by
  filter_upwards [(bulkCollar_isOpen t0 δ ε).mem_nhds hz] with y hy
  exact gaussianVacuum_block_unit hg hy

theorem christoffel_congr_germ {g q : Metric} {z : Bulk}
    (he : g =ᶠ[𝓝 z] q) (a b c : Fin 5) :
    (fun y => christoffel g y a b c) =ᶠ[𝓝 z]
      (fun y => christoffel q y a b c) := by
  filter_upwards [he.eventuallyEq_nhds] with y hy
  have hv : g y = q y := hy.eq_of_nhds
  have hd (i j k : Fin 5) : bulkPartial (fun w => g w i j) k y =
      bulkPartial (fun w => q w i j) k y := by
    apply bulkPartial_congr_of_eventuallyEq
    filter_upwards [hy] with w hw
    exact congrArg (fun M : BulkMatrix => M i j) hw
  simp only [christoffel, inverseMetric, hv, hd]

theorem ricci_congr_germ {g q : Metric} {z : Bulk} (he : g =ᶠ[𝓝 z] q) :
    ricci g z = ricci q z := by
  have hc (a b c : Fin 5) := christoffel_congr_germ he a b c
  have hv (a b c : Fin 5) : christoffel g z a b c = christoffel q z a b c :=
    (hc a b c).eq_of_nhds
  have hd (a b c i : Fin 5) :
      bulkPartial (fun y => christoffel g y a b c) i z =
      bulkPartial (fun y => christoffel q y a b c) i z :=
    bulkPartial_congr_of_eventuallyEq _ _ z (hc a b c) i
  ext a b
  simp only [ricci, hd, hv]

theorem gaussianVacuum_block_vacuum {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {z : Bulk} (hz : z ∈ bulkCollar t0 δ ε) :
    ricci (gaussianMetric (metricTangentialBlock g)) z = 0 := by
  rw [← ricci_congr_germ (gaussianVacuum_eq_gaussian_germ hg hz)]
  exact hg.vacuum z hz

theorem boundaryK_eq_block (g : Metric) (t : ℝ) (x : Vec) :
    boundaryK g t x = gaussianSecondForm (metricTangentialBlock g) (bulkPoint 0 t x) := rfl

theorem gaussianVacuum_boundary_analytic {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => boundaryK g z.1 z.2) (spacetimeSlab t0 δ) := by
  intro z hz
  have he : AnalyticAt ℝ (fun w : ℝ × Vec => bulkPoint 0 w.1 w.2) z := by
    rw [← boundaryEmbed_coe]
    exact boundaryEmbed.analyticAt z
  exact (analyticAt_gaussianSecondForm
    (gaussianVacuum_block_analytic hg (boundaryPoint_mem_collar hg hz z.2))).comp
      (f := fun w : ℝ × Vec => bulkPoint 0 w.1 w.2) (x := z) he

theorem gaussianVacuum_boundary_symmetric {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ) (x : Vec) :
    (boundaryK g t x).IsSymm := by
  have hz := boundaryPoint_mem_collar hg ht x
  ext a b
  have he : (fun z => g z b.succ a.succ) =ᶠ[𝓝 (bulkPoint 0 t x)]
      (fun z => g z a.succ b.succ) := by
    filter_upwards [(bulkCollar_isOpen t0 δ ε).mem_nhds hz] with z hz'
    exact (hg.symmetric z hz').apply a.succ b.succ
  change (1 / 2 : ℝ) * bulkPartial (fun z => g z b.succ a.succ) 0
      (bulkPoint 0 t x) = (1 / 2 : ℝ) * bulkPartial (fun z => g z a.succ b.succ) 0
      (bulkPoint 0 t x)
  rw [bulkPartial_congr_of_eventuallyEq _ _ _ he]

theorem gaussianVacuum_boundary_periodic {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ) :
    SpatialPeriodic (boundaryK g t) := by
  intro x i
  ext a b
  have he : (fun r : ℝ => g (bulkPoint r t (x + unitVector i)) a.succ b.succ)
      =ᶠ[𝓝 0] (fun r : ℝ => g (bulkPoint r t x) a.succ b.succ) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hg.radial_radius_pos)
      hg.radial_radius_pos] with r hr
    exact congrArg (fun M : BulkMatrix => M a.succ b.succ) (hg.periodic r hr t ht x i)
  have hd := he.deriv_eq
  rw [bulkPartial_radial_restrict (analyticAt_matrix_entry
      (hg.analytic _ (boundaryPoint_mem_collar hg ht (x + unitVector i))) a.succ b.succ),
    bulkPartial_radial_restrict (analyticAt_matrix_entry
      (hg.analytic _ (boundaryPoint_mem_collar hg ht x)) a.succ b.succ)] at hd
  change (1 / 2 : ℝ) * bulkPartial (fun z => g z a.succ b.succ) 0
      (bulkPoint 0 t (x + unitVector i)) =
    (1 / 2 : ℝ) * bulkPartial (fun z => g z a.succ b.succ) 0 (bulkPoint 0 t x)
  rw [hd]

theorem gaussianVacuum_block_flat {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ) (x : Vec) :
    metricTangentialBlock g (bulkPoint 0 t x) = eta4Matrix := by
  ext a b
  exact hg.induced t ht x a b

theorem gaussianVacuum_block_tangent_zero {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) (a b c : Fin 4) :
    bulkPartial (fun y => metricTangentialBlock g y a b) c.succ (bulkPoint 0 t x) = 0 := by
  apply bulkPartial_tangent_zero
    (analyticAt_matrix_entry (gaussianVacuum_block_analytic hg
      (boundaryPoint_mem_collar hg ht x)) a b) (c := eta4 a b)
  filter_upwards [boundary_time_eventually (x := x) ht] with z hz
  exact hg.induced z.1 hz z.2 a b

theorem gaussianVacuum_connection_zero {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) (a b c : Fin 4) :
    gaussianTangentialChristoffel (metricTangentialBlock g) (bulkPoint 0 t x) a b c = 0 := by
  simp only [gaussianTangentialChristoffel, gaussianVacuum_block_tangent_zero hg ht x,
    zero_add, sub_zero, mul_zero, Finset.sum_const_zero]

theorem gaussianVacuum_connection_tangent_zero {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) (a b c d : Fin 4) :
    bulkPartial (fun y => gaussianTangentialChristoffel (metricTangentialBlock g) y a b c)
      d.succ (bulkPoint 0 t x) = 0 := by
  have hz := boundaryPoint_mem_collar hg ht x
  apply bulkPartial_tangent_zero
    (analyticAt_gaussianTangentialChristoffel (gaussianVacuum_block_analytic hg hz)
      (gaussianVacuum_block_unit hg hz) a b c) (c := (0 : ℝ))
  filter_upwards [boundary_time_eventually (x := x) ht] with z hz'
  exact gaussianVacuum_connection_zero hg hz' z.2 a b c

theorem gaussianVacuum_boundary_hamiltonian {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ) (x : Vec) :
    boundaryHamiltonian (boundaryK g) t x = 0 := by
  have hz := boundaryPoint_mem_collar hg ht x
  change lorentzSquare4 (gaussianSecondForm (metricTangentialBlock g) (bulkPoint 0 t x)) -
    (lorentzTrace4 (gaussianSecondForm (metricTangentialBlock g) (bulkPoint 0 t x))) ^ 2 = 0
  exact gaussian_hamiltonian_flat (gaussianVacuum_block_analytic hg hz)
    (gaussianVacuum_block_unit_germ hg hz) (gaussianVacuum_block_flat hg ht x)
    (gaussianVacuum_boundary_symmetric hg ht x)
    (gaussianVacuum_connection_zero hg ht x)
    (gaussianVacuum_connection_tangent_zero hg ht x)
    (gaussianVacuum_block_vacuum hg hz)

theorem gaussianVacuum_shape_tangent {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) (a b c : Fin 4) :
    bulkPartial (fun y => gaussianShapeOperator (metricTangentialBlock g) y a b)
      c.succ (bulkPoint 0 t x) =
    lorentzSign4 a * boundaryPartial (fun s y => boundaryK g s y a b) c t x := by
  have hz := boundaryPoint_mem_collar hg ht x
  have hs := analyticAt_matrix_entry (analyticAt_gaussianShape
    (gaussianVacuum_block_analytic hg hz) (gaussianVacuum_block_unit hg hz)) a b
  rw [← boundaryPartial_restrict hs]
  have he : (fun z : ℝ × Vec => gaussianShapeOperator (metricTangentialBlock g)
      (bulkPoint 0 z.1 z.2) a b) =ᶠ[𝓝 (t, x)]
      (fun z => lorentzSign4 a * boundaryK g z.1 z.2 a b) := by
    filter_upwards [boundary_time_eventually (x := x) ht] with z hz'
    exact gaussianShape_at_flat (gaussianVacuum_block_flat hg hz' z.2) a b
  rw [boundaryPartial_congr
    (f := fun s y => gaussianShapeOperator (metricTangentialBlock g) (bulkPoint 0 s y) a b)
    (q := fun s y => lorentzSign4 a * boundaryK g s y a b) he]
  exact boundaryPartial_const_mul
    (analyticAt_matrix_entry (gaussianVacuum_boundary_analytic hg (t, x) ht) a b)
      (lorentzSign4 a) c

theorem gaussianVacuum_boundary_codazzi {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) {t : ℝ} (ht : t ∈ timeInterval t0 δ)
    (x : Vec) (a : Fin 4) : boundaryCodazzi (boundaryK g) t x a = 0 := by
  have hz := boundaryPoint_mem_collar hg ht x
  have hc := gaussianCodazziComponent_zero_of_vacuum (metricTangentialBlock g)
    (bulkPoint 0 t x) (gaussianVacuum_block_vacuum hg hz) a
  rw [boundaryCodazzi_expanded (gaussianVacuum_boundary_analytic hg (t, x) ht)]
  simpa only [gaussianCodazziComponent, gaussianVacuum_shape_tangent hg ht x,
    gaussianVacuum_connection_zero hg ht x, zero_mul, sub_self,
    Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib] using hc

/-- Actual vacuum geometry supplies every field on the original supplied interval. -/
theorem gaussianVacuum_boundaryAdmissible {ρ t0 δ ε : ℝ} {g : Metric}
    (hg : GaussianVacuum ρ t0 δ ε g) :
    BoundaryAdmissible ρ t0 δ (boundaryK g) where
  radius_pos := hg.time_radius_pos
  analytic := gaussianVacuum_boundary_analytic hg
  periodic := fun t ht => gaussianVacuum_boundary_periodic hg ht
  symmetric := fun t ht x => gaussianVacuum_boundary_symmetric hg ht x
  momentum_constraint := fun t ht x a => gaussianVacuum_boundary_codazzi hg ht x a
  hamiltonian := fun t ht x => gaussianVacuum_boundary_hamiltonian hg ht x
  beta_initial := hg.beta_initial
  beta_time_initial := hg.beta_time_initial

end
end NSEGR.Assembly
