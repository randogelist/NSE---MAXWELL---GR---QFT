import GRAssembly.NativeGaussianMetricCurvature

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

/-- Skewness with respect to a symmetric bilinear matrix, as a concrete
matrix equation. -/
def MetricSkew (G A : BulkMatrix) : Prop := A.transpose * G + G * A = 0

theorem MetricSkew.zero (G : BulkMatrix) : MetricSkew G 0 := by
  simp [MetricSkew]

theorem MetricSkew.add {G A B : BulkMatrix} (hA : MetricSkew G A)
    (hB : MetricSkew G B) : MetricSkew G (A + B) := by
  unfold MetricSkew at *
  calc
    (A + B).transpose * G + G * (A + B) =
        (A.transpose * G + G * A) + (B.transpose * G + G * B) := by
      rw [Matrix.transpose_add]
      noncomm_ring
    _ = 0 := by rw [hA, hB, add_zero]

theorem MetricSkew.neg {G A : BulkMatrix} (hA : MetricSkew G A) :
    MetricSkew G (-A) := by
  unfold MetricSkew at *
  simpa only [Matrix.transpose_neg, neg_mul, mul_neg, ← neg_add, neg_zero]
    using congrArg Neg.neg hA

theorem MetricSkew.sub {G A B : BulkMatrix} (hA : MetricSkew G A)
    (hB : MetricSkew G B) : MetricSkew G (A - B) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

theorem MetricSkew.smul {G A : BulkMatrix} (hA : MetricSkew G A) (r : ℝ) :
    MetricSkew G (r • A) := by
  unfold MetricSkew at *
  simpa only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    ← smul_add, smul_zero] using congrArg (fun M : BulkMatrix => r • M) hA

theorem MetricSkew.sum {G : BulkMatrix} {f : Fin 5 → BulkMatrix}
    (hf : ∀ i, MetricSkew G (f i)) : MetricSkew G (∑ i, f i) := by
  classical
  have hfin : ∀ s : Finset (Fin 5), MetricSkew G (∑ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using MetricSkew.zero G
    | @insert a s ha ih => simpa only [Finset.sum_insert ha] using (hf a).add ih
  exact hfin Finset.univ

/-- Differentiating metric skewness with a compatible connection proves that
the connection derivative of an endomorphism remains metric-skew. -/
theorem MetricSkew.connectionDerivative {G R : Bulk → BulkMatrix} {z : Bulk}
    (hG : AnalyticAt ℝ G z) (hR : AnalyticAt ℝ R z)
    (hS : ∀ᶠ y in 𝓝 z, MetricSkew (G y) (R y))
    (A : BulkMatrix) (i : Fin 5)
    (hC : coordDeriv G i z = A.transpose * G z + G z * A) :
    MetricSkew (G z) (coordDeriv R i z + matrixCommutator A (R z)) := by
  have he : (fun y => (R y).transpose * G y + G y * R y) =ᶠ[𝓝 z]
      (fun _ => (0 : BulkMatrix)) := hS
  have hd := coordDeriv_congr_germ he i
  rw [coordDeriv_const,
    coordDeriv_add (f := fun y => (R y).transpose * G y)
      (q := fun y => G y * R y) ((analyticAt_bulkTranspose hR).mul hG) (hG.mul hR),
    coordDeriv_matrix_mul (f := fun y => (R y).transpose) (q := G)
      (analyticAt_bulkTranspose hR) hG,
    coordDeriv_matrix_mul (f := G) (q := R) hG hR,
    coordDeriv_bulkTranspose hR, hC] at hd
  have h0 : (R z).transpose * G z + G z * R z = 0 := hS.self_of_nhds
  unfold MetricSkew
  have ha :
      (coordDeriv R i z + matrixCommutator A (R z)).transpose * G z +
        G z * (coordDeriv R i z + matrixCommutator A (R z)) =
      (((coordDeriv R i z).transpose * G z +
        (R z).transpose * (A.transpose * G z + G z * A)) +
       ((A.transpose * G z + G z * A) * R z + G z * coordDeriv R i z)) -
       A.transpose * ((R z).transpose * G z + G z * R z) -
       ((R z).transpose * G z + G z * R z) * A := by
    unfold matrixCommutator
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
    noncomm_ring
  rw [ha, hd, h0]
  simp

/-- The actual covariant curvature derivative, with the two form-index
corrections explicitly included. -/
def covariantCurvature (g : Metric) (z : Bulk) (e c d : Fin 5) : BulkMatrix :=
  coordDeriv (fun y => metricCurvature g y c d) e z +
    matrixCommutator (metricConnection g e z) (metricCurvature g z c d) -
    (∑ u : Fin 5, metricConnection g e z u c • metricCurvature g z u d) -
    ∑ u : Fin 5, metricConnection g e z u d • metricCurvature g z c u

theorem covariantCurvature_metricSkew {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (e c d : Fin 5) :
    MetricSkew (g z) (covariantCurvature g z e c d) := by
  have hs (i j : Fin 5) : MetricSkew (g z) (metricCurvature g z i j) :=
    metric_curvature_skew_lower hg hS hN i j
  have he : ∀ᶠ y in 𝓝 z, MetricSkew (g y) (metricCurvature g y c d) := by
    filter_upwards [hg.eventually_analyticAt, eventually_eventually_nhds.2 hS,
      eventually_eventually_nhds.2 hN] with y hy hs hn
    exact metric_curvature_skew_lower hy hs hn c d
  have hd := MetricSkew.connectionDerivative hg
    (analyticAt_metricCurvature hg hN.self_of_nhds c d) he
    (metricConnection g e z) e (metric_connection_compatible hg hS hN.self_of_nhds e)
  exact (hd.sub (MetricSkew.sum (fun u => (hs u d).smul _))).sub
    (MetricSkew.sum (fun u => (hs c u).smul _))

theorem covariantCurvature_first_form_skew (g : Metric) (z : Bulk)
    (e c d : Fin 5) :
    covariantCurvature g z e d c = -covariantCurvature g z e c d := by
  have he : (fun y => metricCurvature g y d c) =
      (fun y => -metricCurvature g y c d) := by
    funext y
    exact metricCurvature_skew_last g y d c
  unfold covariantCurvature
  rw [he]
  have hder : coordDeriv (fun y => -metricCurvature g y c d) e z =
      -coordDeriv (fun y => metricCurvature g y c d) e z := by simp [coordDeriv]
  rw [hder, metricCurvature_skew_last g z d c]
  have hsum1 :
      (∑ u : Fin 5, metricConnection g e z u d • metricCurvature g z u c) =
        -(∑ u : Fin 5, metricConnection g e z u d • metricCurvature g z c u) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [metricCurvature_skew_last g z u c, smul_neg]
  have hsum2 :
      (∑ u : Fin 5, metricConnection g e z u c • metricCurvature g z d u) =
        -(∑ u : Fin 5, metricConnection g e z u c • metricCurvature g z u d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [metricCurvature_skew_last g z d u, smul_neg]
  rw [hsum1, hsum2]
  unfold matrixCommutator
  noncomm_ring

/-- Full covariant differential Bianchi, including all form-index terms. -/
theorem covariantCurvature_bianchi {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det)
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (e c d : Fin 5) :
    covariantCurvature g z e c d + covariantCurvature g z c d e +
      covariantCurvature g z d e c = 0 := by
  have h0 := metricCurvature_differential_bianchi hg hN e c d
  have hs1 :
      (∑ u : Fin 5, metricConnection g e z u c • metricCurvature g z u d) =
        -(∑ u : Fin 5, metricConnection g c z u e • metricCurvature g z d u) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [metricConnection_torsion hS u e c, metricCurvature_skew_last g z d u,
      smul_neg, neg_neg]
  have hs2 :
      (∑ u : Fin 5, metricConnection g e z u d • metricCurvature g z c u) =
        -(∑ u : Fin 5, metricConnection g d z u e • metricCurvature g z u c) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [metricConnection_torsion hS u e d, metricCurvature_skew_last g z u c,
      smul_neg, neg_neg]
  have hs3 :
      (∑ u : Fin 5, metricConnection g c z u d • metricCurvature g z u e) =
        -(∑ u : Fin 5, metricConnection g d z u c • metricCurvature g z e u) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [metricConnection_torsion hS u c d, metricCurvature_skew_last g z e u,
      smul_neg, neg_neg]
  unfold covariantCurvature
  rw [hs1, hs2, hs3]
  have ha :
      ((coordDeriv (fun y => metricCurvature g y c d) e z +
          matrixCommutator (metricConnection g e z) (metricCurvature g z c d) -
          -(∑ u : Fin 5, metricConnection g c z u e • metricCurvature g z d u) -
          -(∑ u : Fin 5, metricConnection g d z u e • metricCurvature g z u c)) +
        (coordDeriv (fun y => metricCurvature g y d e) c z +
          matrixCommutator (metricConnection g c z) (metricCurvature g z d e) -
          -(∑ u : Fin 5, metricConnection g d z u c • metricCurvature g z e u) -
          (∑ u : Fin 5, metricConnection g c z u e • metricCurvature g z d u))) +
        (coordDeriv (fun y => metricCurvature g y e c) d z +
          matrixCommutator (metricConnection g d z) (metricCurvature g z e c) -
          (∑ u : Fin 5, metricConnection g d z u e • metricCurvature g z u c) -
          (∑ u : Fin 5, metricConnection g d z u c • metricCurvature g z e u)) =
        (coordDeriv (fun y => metricCurvature g y c d) e z +
          matrixCommutator (metricConnection g e z) (metricCurvature g z c d)) +
        (coordDeriv (fun y => metricCurvature g y d e) c z +
          matrixCommutator (metricConnection g c z) (metricCurvature g z d e)) +
        (coordDeriv (fun y => metricCurvature g y e c) d z +
          matrixCommutator (metricConnection g d z) (metricCurvature g z e c)) := by
    abel
  exact ha.trans h0

/-- Covariant derivative of the literal native Ricci matrix. -/
def covariantRicci (g : Metric) (z : Bulk) (e : Fin 5) : BulkMatrix :=
  coordDeriv (ricci g) e z - (metricConnection g e z).transpose * ricci g z -
    ricci g z * metricConnection g e z

/-- The connection terms on the contracted upper/form index cancel.
This finite algebra lemma does not assume any differential or curvature law. -/
theorem curvature_trace_algebra (R D : Fin 5 → Fin 5 → BulkMatrix)
    (A : BulkMatrix) (b d : Fin 5) :
    (∑ c : Fin 5,
      (D c d + matrixCommutator A (R c d) -
        (∑ u : Fin 5, A u c • R u d) -
        ∑ u : Fin 5, A u d • R c u) c b) =
      (∑ c : Fin 5, D c d c b) -
      (∑ u : Fin 5, A u b * (∑ c : Fin 5, R c d c u)) -
      ∑ u : Fin 5, (∑ c : Fin 5, R c u c b) * A u d := by
  simp only [matrixCommutator, Matrix.add_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_succ]
  ring

theorem coordDeriv_nativeRicci_entry {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (e b d : Fin 5) :
    (coordDeriv (ricci g) e z) b d =
      ∑ c : Fin 5, (coordDeriv (fun y => metricCurvature g y c d) e z) c b := by
  have he : (fun y => ricci g y b d) =ᶠ[𝓝 z]
      (fun y => ∑ c : Fin 5, metricCurvature g y c d c b) := by
    filter_upwards [hg.eventually_analyticAt, eventually_eventually_nhds.2 hS, hN]
      with y hy hs hn
    exact nativeRicci_eq_curvature_trace hy hn hs b d
  rw [coordDeriv_matrix_entry (analyticAt_nativeRicci hg hN.self_of_nhds)]
  rw [Assembly.bulkPartial_congr_of_eventuallyEq _ _ _ he]
  rw [Assembly.bulkPartial_sum (fun c => Assembly.analyticAt_matrix_entry
    (analyticAt_metricCurvature hg hN.self_of_nhds c d) c b)]
  apply Finset.sum_congr rfl
  intro c hc
  exact (coordDeriv_matrix_entry (analyticAt_metricCurvature hg hN.self_of_nhds c d)
    e c b).symm

theorem covariantRicci_eq_curvature_trace {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (e b d : Fin 5) :
    covariantRicci g z e b d =
      ∑ c : Fin 5, covariantCurvature g z e c d c b := by
  have ha := curvature_trace_algebra (fun c d => metricCurvature g z c d)
    (fun c d => coordDeriv (fun y => metricCurvature g y c d) e z)
    (metricConnection g e z) b d
  unfold covariantRicci
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [coordDeriv_nativeRicci_entry hg hS hN]
  simp_rw [nativeRicci_eq_curvature_trace hg hN.self_of_nhds hS]
  exact ha.symm

/-- One contraction of the full covariant Bianchi identity. -/
theorem covariantRicci_first_contracted_bianchi {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (e b d : Fin 5) :
    covariantRicci g z e b d - covariantRicci g z d b e +
      (∑ c : Fin 5, covariantCurvature g z c d e c b) = 0 := by
  rw [covariantRicci_eq_curvature_trace hg hS hN,
    covariantRicci_eq_curvature_trace hg hS hN]
  have hs :
      (∑ c : Fin 5,
        (covariantCurvature g z e c d c b + covariantCurvature g z c d e c b +
          covariantCurvature g z d e c c b)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have he := congrArg (fun A : BulkMatrix => A c b)
      (covariantCurvature_bianchi hg hN.self_of_nhds hS e c d)
    simpa only [Matrix.add_apply, Matrix.zero_apply] using he
  have hsk (c : Fin 5) : covariantCurvature g z d e c c b =
      -covariantCurvature g z d c e c b := by
    exact congrArg (fun A : BulkMatrix => A c b)
      (covariantCurvature_first_form_skew g z d c e)
  simp_rw [hsk] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hs
  linear_combination hs

theorem coordDeriv_bulkInverse {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) (i : Fin 5) :
    coordDeriv (fun y => (g y)⁻¹) i z =
      -((g z)⁻¹ * coordDeriv g i z * (g z)⁻¹) := by
  have hu : IsUnit (g z) := (g z).isUnit_iff_isUnit_det.mpr hN
  have hi : HasFDerivAt (fun H : BulkMatrix => H⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ BulkMatrix (g z)⁻¹ (g z)⁻¹) (g z) := by
    have he : (fun H : BulkMatrix => H⁻¹) = Ring.inverse := by
      funext H
      exact Matrix.nonsing_inv_eq_ringInverse H
    rw [he]
    simpa only [Matrix.coe_units_inv, IsUnit.unit_spec]
      using (hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit)
  have hd := hi.comp z hg.differentiableAt.hasFDerivAt
  unfold coordDeriv
  have hd' : fderiv ℝ (fun y => (g y)⁻¹) z =
      (-ContinuousLinearMap.mulLeftRight ℝ BulkMatrix (g z)⁻¹ (g z)⁻¹).comp
        (fderiv ℝ g z) := by
    simpa only [Function.comp_def] using hd.fderiv
  rw [hd']
  rfl

theorem coordDeriv_inverse_compatible {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : IsUnit (g z).det) (i : Fin 5) :
    coordDeriv (fun y => (g y)⁻¹) i z =
      -(metricConnection g i z * (g z)⁻¹) -
        (g z)⁻¹ * (metricConnection g i z).transpose := by
  rw [coordDeriv_bulkInverse hg hN,
    metric_connection_compatible hg hS hN i]
  calc
    -((g z)⁻¹ * ((metricConnection g i z).transpose * g z +
        g z * metricConnection g i z) * (g z)⁻¹) =
      -((g z)⁻¹ * (metricConnection g i z).transpose * (g z * (g z)⁻¹) +
        ((g z)⁻¹ * g z) * metricConnection g i z * (g z)⁻¹) := by noncomm_ring
    _ = _ := by
      rw [Matrix.mul_nonsing_inv _ hN, Matrix.nonsing_inv_mul _ hN]
      noncomm_ring

/-- Finite scalar-contraction derivative algebra. The matrix pairing expands
to the same polynomial on both sides. -/
theorem scalar_contraction_derivative_algebra (H S D A : BulkMatrix)
    (hH : H.IsSymm) (hS : S.IsSymm) :
    (∑ a : Fin 5, ∑ b : Fin 5,
      ((-(A * H) - H * A.transpose) a b * S a b + H a b * D a b)) =
    ∑ a : Fin 5, ∑ b : Fin 5, H a b * (D - A.transpose * S - S * A) a b := by
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  ring

theorem bulkPartial_scalarCurvature {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (e : Fin 5) :
    bulkPartial (scalarCurvature g) e z =
      ∑ a : Fin 5, ∑ b : Fin 5, (g z)⁻¹ a b * covariantRicci g z e a b := by
  have hi := analyticAt_bulkMatrix_inverse hg hN.self_of_nhds
  have hr := analyticAt_nativeRicci hg hN.self_of_nhds
  have hI : ((g z)⁻¹).IsSymm := by
    change ((g z)⁻¹).transpose = (g z)⁻¹
    rw [Matrix.transpose_nonsing_inv, hS.self_of_nhds.eq]
  have hd : bulkPartial (scalarCurvature g) e z =
      ∑ a : Fin 5, ∑ b : Fin 5,
        ((coordDeriv (fun y => (g y)⁻¹) e z) a b * ricci g z a b +
          (g z)⁻¹ a b * (coordDeriv (ricci g) e z) a b) := by
    unfold scalarCurvature inverseMetric
    rw [Assembly.bulkPartial_sum (fun a => by
      apply Finset.analyticAt_fun_sum
      intro b hb
      exact (Assembly.analyticAt_matrix_entry hi a b).mul
        (Assembly.analyticAt_matrix_entry hr a b))]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Assembly.bulkPartial_sum
      (f := fun b y => (g y)⁻¹ a b * ricci g y a b) (fun b =>
      (Assembly.analyticAt_matrix_entry hi a b).mul
        (Assembly.analyticAt_matrix_entry hr a b))]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Assembly.bulkPartial_mul
      (f := fun y => (g y)⁻¹ a b) (q := fun y => ricci g y a b)
      (Assembly.analyticAt_matrix_entry hi a b)
      (Assembly.analyticAt_matrix_entry hr a b)]
    rw [← coordDeriv_matrix_entry hi, ← coordDeriv_matrix_entry hr]
  rw [hd, coordDeriv_inverse_compatible hg hS hN.self_of_nhds e]
  exact scalar_contraction_derivative_algebra (g z)⁻¹ (ricci g z)
    (coordDeriv (ricci g) e z) (metricConnection g e z) hI
    (nativeRicci_symmetric hg hS hN)

theorem MetricSkew.inverse_pairing {G A : BulkMatrix}
    (hA : MetricSkew G A) (hN : IsUnit G.det) (a d : Fin 5) :
    (∑ b : Fin 5, G⁻¹ b d * A a b) =
      -(∑ c : Fin 5, G⁻¹ a c * A d c) := by
  have hs := congrArg (fun M : BulkMatrix => G⁻¹ * M * G⁻¹) hA
  have he : G⁻¹ * (A.transpose * G + G * A) * G⁻¹ =
      G⁻¹ * A.transpose + A * G⁻¹ := by
    calc
      _ = G⁻¹ * A.transpose * (G * G⁻¹) + (G⁻¹ * G) * A * G⁻¹ := by
        noncomm_ring
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.nonsing_inv_mul _ hN]; simp
  change G⁻¹ * (A.transpose * G + G * A) * G⁻¹ = G⁻¹ * 0 * G⁻¹ at hs
  rw [he] at hs
  have hv := congrArg (fun M : BulkMatrix => M a d) hs
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_mul] at hv
  have hc : (∑ b : Fin 5, G⁻¹ b d * A a b) = ∑ b : Fin 5, A a b * G⁻¹ b d := by
    apply Finset.sum_congr rfl
    intro b hb
    exact mul_comm _ _
  rw [hc]
  linarith

theorem metricSkew_double_contraction (G : BulkMatrix) (hN : IsUnit G.det)
    (T : Fin 5 → Fin 5 → BulkMatrix) (hT : ∀ a d, MetricSkew G (T a d)) :
    (∑ b : Fin 5, ∑ d : Fin 5, G⁻¹ b d * (∑ a : Fin 5, T a d a b)) =
      -(∑ a : Fin 5, ∑ c : Fin 5, G⁻¹ a c * (∑ d : Fin 5, T a d d c)) := by
  have hs :
      (∑ a : Fin 5, ∑ d : Fin 5,
        ((∑ b : Fin 5, G⁻¹ b d * T a d a b) +
          ∑ c : Fin 5, G⁻¹ a c * T a d d c)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro d hd
    have he := (hT a d).inverse_pairing hN a d
    linarith
  simp only [Fin.sum_univ_succ] at hs ⊢
  linear_combination hs

/-- Contracted Bianchi for the literal native Ricci and scalar-curvature
definitions. Every curvature and derivative premise has been discharged
from the analytic, symmetric, nondegenerate coordinate metric. -/
theorem native_contracted_bianchi {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (e : Fin 5) :
    2 * (∑ a : Fin 5, ∑ c : Fin 5, (g z)⁻¹ a c * covariantRicci g z a c e) =
      bulkPartial (scalarCurvature g) e z := by
  have hI : ((g z)⁻¹).IsSymm := by
    change ((g z)⁻¹).transpose = (g z)⁻¹
    rw [Matrix.transpose_nonsing_inv, hS.self_of_nhds.eq]
  have hc := metricSkew_double_contraction (g z) hN.self_of_nhds
    (fun a d => covariantCurvature g z a d e)
    (fun a d => covariantCurvature_metricSkew hg hS hN a d e)
  simp_rw [← covariantRicci_eq_curvature_trace hg hS hN] at hc
  have hm :
      (∑ b : Fin 5, ∑ d : Fin 5, (g z)⁻¹ b d * covariantRicci g z d b e) =
        ∑ a : Fin 5, ∑ c : Fin 5, (g z)⁻¹ a c * covariantRicci g z a c e := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc'
    rw [hI.apply a c]
  have hw :
      (∑ b : Fin 5, ∑ d : Fin 5, (g z)⁻¹ b d *
        (covariantRicci g z e b d - covariantRicci g z d b e +
          ∑ c : Fin 5, covariantCurvature g z c d e c b)) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    apply Finset.sum_eq_zero
    intro d hd
    rw [covariantRicci_first_contracted_bianchi hg hS hN e b d, mul_zero]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hw
  rw [hm, hc] at hw
  rw [bulkPartial_scalarCurvature hg hS hN e]
  linarith

end
end NSEGR.NativeLiterature
