import GRAssembly.NativeGaussianBianchi

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

/-- The literal native Christoffel connection arranged as matrices. -/
def metricConnection (g : Metric) (i : Fin 5) (z : Bulk) : BulkMatrix :=
  fun a b => christoffel g z a i b

/-- Lowered Christoffel expression, before multiplication by the inverse. -/
def loweredConnection (g : Metric) (i : Fin 5) (z : Bulk) : BulkMatrix :=
  fun a b => (1 / 2 : ℝ) *
    (bulkPartial (fun y => g y a b) i z + bulkPartial (fun y => g y a i) b z -
      bulkPartial (fun y => g y i b) a z)

theorem metricConnection_eq_inverse_mul (g : Metric) (i : Fin 5) (z : Bulk) :
    metricConnection g i z = (g z)⁻¹ * loweredConnection g i z := by
  ext a b
  simp only [metricConnection, loweredConnection, christoffel, inverseMetric,
    Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem coordDeriv_matrix_entry {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (i a b : Fin 5) :
    (coordDeriv g i z) a b = bulkPartial (fun y => g y a b) i z := by
  exact (Assembly.matrix_entry_fderiv hg.differentiableAt (bulkBasis i) a b).symm

theorem bulkPartial_entry_symm {g : Metric} {z : Bulk}
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (i a b : Fin 5) :
    bulkPartial (fun y => g y b a) i z = bulkPartial (fun y => g y a b) i z := by
  apply Assembly.bulkPartial_congr_of_eventuallyEq
  exact hS.mono (fun y hy => hy.apply a b)

theorem loweredConnection_add_transpose {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (i : Fin 5) :
    loweredConnection g i z + (loweredConnection g i z).transpose =
      coordDeriv g i z := by
  ext a b
  rw [coordDeriv_matrix_entry hg i a b]
  simp only [Matrix.add_apply, Matrix.transpose_apply, loweredConnection]
  rw [bulkPartial_entry_symm hS i a b,
    bulkPartial_entry_symm hS a i b,
    bulkPartial_entry_symm hS b a i]
  ring

theorem metric_mul_connection {g : Metric} {z : Bulk}
    (hN : IsUnit (g z).det) (i : Fin 5) :
    g z * metricConnection g i z = loweredConnection g i z := by
  rw [metricConnection_eq_inverse_mul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hN, one_mul]

/-- Metric compatibility derived from the literal native Christoffel formula. -/
theorem metric_connection_compatible {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : IsUnit (g z).det) (i : Fin 5) :
    coordDeriv g i z =
      (metricConnection g i z).transpose * g z + g z * metricConnection g i z := by
  calc
    coordDeriv g i z =
        loweredConnection g i z + (loweredConnection g i z).transpose :=
      (loweredConnection_add_transpose hg hS i).symm
    _ = g z * metricConnection g i z + (g z * metricConnection g i z).transpose := by
      rw [metric_mul_connection hN i]
    _ = _ := by
      rw [Matrix.transpose_mul, hS.self_of_nhds.eq]
      exact add_comm _ _

theorem analyticAt_bulkMatrix_inverse {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) :
    AnalyticAt ℝ (fun y => (g y)⁻¹) z := by
  have hu : IsUnit (g z) := (g z).isUnit_iff_isUnit_det.mpr hN
  have hi : AnalyticAt ℝ (fun H : BulkMatrix => H⁻¹) (g z) := by
    have he : (fun H : BulkMatrix => H⁻¹) = Ring.inverse := by
      funext H
      exact Matrix.nonsing_inv_eq_ringInverse H
    rw [he]
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) hu.unit)
  exact hi.comp hg

theorem analyticAt_nativeChristoffel {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) (a b c : Fin 5) :
    AnalyticAt ℝ (fun y => christoffel g y a b c) z := by
  have hi := analyticAt_bulkMatrix_inverse hg hN
  unfold christoffel inverseMetric
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact (Assembly.analyticAt_matrix_entry hi a d).mul
    (((Assembly.analyticAt_bulkPartial (Assembly.analyticAt_matrix_entry hg d c) b).add
      (Assembly.analyticAt_bulkPartial (Assembly.analyticAt_matrix_entry hg d b) c)).sub
        (Assembly.analyticAt_bulkPartial (Assembly.analyticAt_matrix_entry hg b c) d))

theorem analyticAt_metricConnection {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) (i : Fin 5) :
    AnalyticAt ℝ (metricConnection g i) z := by
  apply Assembly.analyticAt_matrix_of_entries
  intro a b
  exact analyticAt_nativeChristoffel hg hN a i b

theorem analyticAt_nativeRicci {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) :
    AnalyticAt ℝ (ricci g) z := by
  apply Assembly.analyticAt_matrix_of_entries
  intro a b
  have hc := analyticAt_nativeChristoffel hg hN
  unfold ricci
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro c hc'
    exact (Assembly.analyticAt_bulkPartial (hc c a b) c).sub
      (Assembly.analyticAt_bulkPartial (hc c a c) b)
  · apply Finset.analyticAt_fun_sum
    intro c hc'
    apply Finset.analyticAt_fun_sum
    intro d hd
    exact ((hc c c d).mul (hc d a b)).sub ((hc c b d).mul (hc d a c))

/-- Torsion vanishes for the actual metric connection. -/
theorem metricConnection_torsion {g : Metric} {z : Bulk}
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (a b c : Fin 5) :
    metricConnection g b z a c = metricConnection g c z a b := by
  unfold metricConnection christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [bulkPartial_entry_symm hS d b c]
  ring

/-- The literal native metric curvature as an endomorphism-valued two-form. -/
def metricCurvature (g : Metric) (z : Bulk) (c d : Fin 5) : BulkMatrix :=
  connectionCurvature (metricConnection g) z c d

theorem analyticAt_metricCurvature {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) (c d : Fin 5) :
    AnalyticAt ℝ (fun y => metricCurvature g y c d) z :=
  analyticAt_connectionCurvature (analyticAt_metricConnection hg hN) c d

theorem metricCurvature_skew_last (g : Metric) (z : Bulk) (c d : Fin 5) :
    metricCurvature g z c d = -metricCurvature g z d c := by
  unfold metricCurvature connectionCurvature matrixCommutator
  noncomm_ring

/-- The differential Bianchi identity instantiated at the actual Christoffel
connection. The missing form-index corrections are handled by torsion in the
fully covariant identity. -/
theorem metricCurvature_differential_bianchi {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det) (e c d : Fin 5) :
    (coordDeriv (fun y => metricCurvature g y c d) e z +
      matrixCommutator (metricConnection g e z) (metricCurvature g z c d)) +
    (coordDeriv (fun y => metricCurvature g y d e) c z +
      matrixCommutator (metricConnection g c z) (metricCurvature g z d e)) +
    (coordDeriv (fun y => metricCurvature g y e c) d z +
      matrixCommutator (metricConnection g d z) (metricCurvature g z e c)) = 0 :=
  connection_differential_bianchi (analyticAt_metricConnection hg hN) e c d

theorem connectionCurvature_entry {Γ : Fin 5 → Bulk → BulkMatrix} {z : Bulk}
    (hΓ : ∀ i, AnalyticAt ℝ (Γ i) z) (a b c d : Fin 5) :
    connectionCurvature Γ z c d a b =
      (bulkPartial (fun y => Γ d y a b) c z -
        bulkPartial (fun y => Γ c y a b) d z) +
      ((∑ e : Fin 5, Γ c z a e * Γ d z e b) -
        ∑ e : Fin 5, Γ d z a e * Γ c z e b) := by
  unfold connectionCurvature matrixCommutator
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  rw [coordDeriv_matrix_entry (hΓ d), coordDeriv_matrix_entry (hΓ c)]

/-- The first Bianchi identity for a torsion-free coordinate connection,
proved by cancellation of the three derivative pairs and six product terms. -/
theorem connection_curvature_first_bianchi
    {Γ : Fin 5 → Bulk → BulkMatrix} {z : Bulk}
    (hΓ : ∀ i, AnalyticAt ℝ (Γ i) z)
    (hT : ∀ᶠ y in 𝓝 z, ∀ a b c : Fin 5, Γ b y a c = Γ c y a b)
    (a b c d : Fin 5) :
    connectionCurvature Γ z c d a b + connectionCurvature Γ z d b a c +
      connectionCurvature Γ z b c a d = 0 := by
  have htz := hT.self_of_nhds
  have hd1 : bulkPartial (fun y => Γ d y a b) c z =
      bulkPartial (fun y => Γ b y a d) c z := by
    apply Assembly.bulkPartial_congr_of_eventuallyEq
    exact hT.mono (fun y hy => hy a d b)
  have hd2 : bulkPartial (fun y => Γ c y a b) d z =
      bulkPartial (fun y => Γ b y a c) d z := by
    apply Assembly.bulkPartial_congr_of_eventuallyEq
    exact hT.mono (fun y hy => hy a c b)
  have hd3 : bulkPartial (fun y => Γ d y a c) b z =
      bulkPartial (fun y => Γ c y a d) b z := by
    apply Assembly.bulkPartial_congr_of_eventuallyEq
    exact hT.mono (fun y hy => hy a d c)
  have hp (e : Fin 5) :
      (Γ c z a e * Γ d z e b - Γ d z a e * Γ c z e b) +
      (Γ d z a e * Γ b z e c - Γ b z a e * Γ d z e c) +
      (Γ b z a e * Γ c z e d - Γ c z a e * Γ b z e d) = 0 := by
    rw [htz e d b, htz e c b, htz e d c]
    ring
  have hs :
      (∑ e : Fin 5, (Γ c z a e * Γ d z e b - Γ d z a e * Γ c z e b)) +
      (∑ e : Fin 5, (Γ d z a e * Γ b z e c - Γ b z a e * Γ d z e c)) +
      (∑ e : Fin 5, (Γ b z a e * Γ c z e d - Γ c z a e * Γ b z e d)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun e he => hp e)
  rw [connectionCurvature_entry hΓ, connectionCurvature_entry hΓ,
    connectionCurvature_entry hΓ, hd1, hd2, hd3]
  simp only [Finset.sum_sub_distrib] at hs
  linear_combination hs

theorem metric_curvature_first_bianchi {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det)
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (a b c d : Fin 5) :
    metricCurvature g z c d a b + metricCurvature g z d b a c +
      metricCurvature g z b c a d = 0 := by
  apply connection_curvature_first_bianchi (analyticAt_metricConnection hg hN)
  exact (eventually_eventually_nhds.2 hS).mono
    (fun y hy a b c => metricConnection_torsion hy a b c)

def bulkTransposeCLM : BulkMatrix →L[ℝ] BulkMatrix :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.transpose
      map_add' := Matrix.transpose_add
      map_smul' := by intro c A; rfl }

theorem analyticAt_bulkTranspose {f : Bulk → BulkMatrix} {z : Bulk}
    (hf : AnalyticAt ℝ f z) : AnalyticAt ℝ (fun y => (f y).transpose) z :=
  (bulkTransposeCLM.analyticAt _).comp hf

theorem coordDeriv_bulkTranspose {f : Bulk → BulkMatrix} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (i : Fin 5) :
    coordDeriv (fun y => (f y).transpose) i z = (coordDeriv f i z).transpose := by
  have hd := bulkTransposeCLM.hasFDerivAt.comp z hf.differentiableAt.hasFDerivAt
  unfold coordDeriv
  have hd' : fderiv ℝ (fun y => (f y).transpose) z =
      bulkTransposeCLM.comp (fderiv ℝ f z) := by
    simpa only [Function.comp_def] using hd.fderiv
  rw [hd']
  rfl

theorem coordDeriv_metric_compatibility {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (i j : Fin 5) :
    coordDeriv (coordDeriv g i) j z =
      ((coordDeriv (metricConnection g i) j z).transpose * g z +
        (metricConnection g i z).transpose * coordDeriv g j z) +
      (coordDeriv g j z * metricConnection g i z +
        g z * coordDeriv (metricConnection g i) j z) := by
  have hΓ : AnalyticAt ℝ (metricConnection g i) z :=
    analyticAt_metricConnection hg hN.self_of_nhds i
  have he : coordDeriv g i =ᶠ[𝓝 z]
      (fun y => (metricConnection g i y).transpose * g y +
        g y * metricConnection g i y) := by
    filter_upwards [hg.eventually_analyticAt, eventually_eventually_nhds.2 hS, hN]
      with y hy hs hn
    exact metric_connection_compatible hy hs hn i
  rw [coordDeriv_congr_germ he j]
  rw [coordDeriv_add ((analyticAt_bulkTranspose hΓ).mul hg) (hg.mul hΓ)]
  rw [coordDeriv_matrix_mul (analyticAt_bulkTranspose hΓ) hg,
    coordDeriv_matrix_mul hg hΓ, coordDeriv_bulkTranspose hΓ]

/-- Curvature is skew with respect to the actual metric. This follows by
differentiating native metric compatibility in both orders. -/
theorem metric_curvature_skew_lower {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (c d : Fin 5) :
    (metricCurvature g z c d).transpose * g z +
      g z * metricCurvature g z c d = 0 := by
  have he := (coordDeriv_metric_compatibility hg hS hN d c).symm.trans
    ((coordDeriv_commute hg d c).trans (coordDeriv_metric_compatibility hg hS hN c d))
  have ha :
      (metricCurvature g z c d).transpose * g z +
        g z * metricCurvature g z c d =
      (((coordDeriv (metricConnection g d) c z).transpose * g z +
        (metricConnection g d z).transpose * coordDeriv g c z) +
       (coordDeriv g c z * metricConnection g d z +
        g z * coordDeriv (metricConnection g d) c z)) -
      (((coordDeriv (metricConnection g c) d z).transpose * g z +
        (metricConnection g c z).transpose * coordDeriv g d z) +
       (coordDeriv g d z * metricConnection g c z +
        g z * coordDeriv (metricConnection g c) d z)) := by
    rw [metric_connection_compatible hg hS hN.self_of_nhds c,
      metric_connection_compatible hg hS hN.self_of_nhds d]
    unfold metricCurvature connectionCurvature matrixCommutator
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
    noncomm_ring
  rw [ha, he, sub_self]

def loweredCurvature (g : Metric) (z : Bulk) (a b c d : Fin 5) : ℝ :=
  (g z * metricCurvature g z c d) a b

theorem loweredCurvature_skew_first {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (a b c d : Fin 5) :
    loweredCurvature g z b a c d = -loweredCurvature g z a b c d := by
  have he := congrArg (fun A : BulkMatrix => A a b)
    (metric_curvature_skew_lower hg hS hN c d)
  have ht : (metricCurvature g z c d).transpose * g z =
      (g z * metricCurvature g z c d).transpose := by
    rw [Matrix.transpose_mul, hS.self_of_nhds.eq]
  rw [ht] at he
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at he
  change (g z * metricCurvature g z c d) b a =
    -(g z * metricCurvature g z c d) a b
  linarith

theorem loweredCurvature_skew_last (g : Metric) (z : Bulk) (a b c d : Fin 5) :
    loweredCurvature g z a b d c = -loweredCurvature g z a b c d := by
  unfold loweredCurvature
  rw [metricCurvature_skew_last g z d c, Matrix.mul_neg]
  rfl

theorem loweredCurvature_first_bianchi {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det)
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (a b c d : Fin 5) :
    loweredCurvature g z a b c d + loweredCurvature g z a c d b +
      loweredCurvature g z a d b c = 0 := by
  unfold loweredCurvature
  simp only [Matrix.mul_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro e he
  have hb := metric_curvature_first_bianchi hg hN hS e b c d
  linear_combination (g z a e) * hb

/-- Pair symmetry obtained from the four first-Bianchi identities and the
two antisymmetries; all indices retain the native convention. -/
theorem loweredCurvature_pair_symmetry {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) (a b c d : Fin 5) :
    loweredCurvature g z a b c d = loweredCurvature g z c d a b := by
  have h1 := loweredCurvature_first_bianchi hg hN.self_of_nhds hS a b c d
  have h2 := loweredCurvature_first_bianchi hg hN.self_of_nhds hS b a c d
  have h3 := loweredCurvature_first_bianchi hg hN.self_of_nhds hS c d a b
  have h4 := loweredCurvature_first_bianchi hg hN.self_of_nhds hS d c a b
  rw [loweredCurvature_skew_first hg hS hN a b c d] at h2
  rw [loweredCurvature_skew_first hg hS hN a c b d,
    loweredCurvature_skew_last g z a c d b,
    loweredCurvature_skew_first hg hS hN b c d a] at h3
  rw [loweredCurvature_skew_first hg hS hN c d a b,
    loweredCurvature_skew_first hg hS hN a d b c,
    loweredCurvature_skew_first hg hS hN b d c a,
    loweredCurvature_skew_last g z b d a c] at h4
  linarith

/-- The curvature contraction is the literal native Ricci tensor, including
the lower-index order in the definition of `NSEGR.ricci`. -/
theorem nativeRicci_eq_curvature_trace {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det)
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (a b : Fin 5) :
    ricci g z a b = ∑ c : Fin 5, metricCurvature g z c b c a := by
  have hΓ := analyticAt_metricConnection hg hN
  have hs (u v w : Fin 5) : christoffel g z u v w = christoffel g z u w v :=
    metricConnection_torsion hS u v w
  have hds (u v w i : Fin 5) :
      bulkPartial (fun y => christoffel g y u v w) i z =
      bulkPartial (fun y => christoffel g y u w v) i z := by
    apply Assembly.bulkPartial_congr_of_eventuallyEq
    exact (eventually_eventually_nhds.2 hS).mono
      (fun y hy => metricConnection_torsion hy u v w)
  symm
  calc
    (∑ c : Fin 5, metricCurvature g z c b c a) =
      ∑ c : Fin 5,
        ((bulkPartial (fun y => christoffel g y c a b) c z -
          bulkPartial (fun y => christoffel g y c a c) b z) +
         ∑ d : Fin 5,
          (christoffel g z c c d * christoffel g z d a b -
            christoffel g z c b d * christoffel g z d a c)) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [metricCurvature, connectionCurvature_entry hΓ]
      change
        (bulkPartial (fun y => christoffel g y c b a) c z -
          bulkPartial (fun y => christoffel g y c c a) b z) +
        ((∑ e : Fin 5, christoffel g z c c e * christoffel g z e b a) -
          ∑ e : Fin 5, christoffel g z c b e * christoffel g z e c a) = _
      rw [hds c b a c, hds c c a b, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [hs d b a, hs d c a]
    _ = ricci g z a b := by
      rw [Finset.sum_add_distrib]
      rfl

theorem nativeRicci_eq_lowered_contraction {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hN : IsUnit (g z).det)
    (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm) (a b : Fin 5) :
    ricci g z a b =
      ∑ i : Fin 5, ∑ j : Fin 5, (g z)⁻¹ i j * loweredCurvature g z j a i b := by
  rw [nativeRicci_eq_curvature_trace hg hN hS]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  change ((g z)⁻¹ * (g z * metricCurvature g z i b)) i a = _
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hN, one_mul]

theorem nativeRicci_symmetric {g : Metric} {z : Bulk}
    (hg : AnalyticAt ℝ g z) (hS : ∀ᶠ y in 𝓝 z, (g y).IsSymm)
    (hN : ∀ᶠ y in 𝓝 z, IsUnit (g y).det) : (ricci g z).IsSymm := by
  have hI : ((g z)⁻¹).IsSymm := by
    change ((g z)⁻¹).transpose = (g z)⁻¹
    rw [Matrix.transpose_nonsing_inv, hS.self_of_nhds.eq]
  apply Matrix.IsSymm.ext
  intro a b
  rw [nativeRicci_eq_lowered_contraction hg hN.self_of_nhds hS b a,
    nativeRicci_eq_lowered_contraction hg hN.self_of_nhds hS a b]
  calc
    (∑ i : Fin 5, ∑ j : Fin 5, (g z)⁻¹ i j * loweredCurvature g z j b i a) =
        ∑ i : Fin 5, ∑ j : Fin 5, (g z)⁻¹ i j * loweredCurvature g z i a j b := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [loweredCurvature_pair_symmetry hg hS hN j b i a]
    _ = ∑ j : Fin 5, ∑ i : Fin 5, (g z)⁻¹ i j * loweredCurvature g z i a j b :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hI.apply i j]

end
end NSEGR.NativeLiterature
