import GRAssembly.NativeCKNormalization
import GRAssembly.GaussianConstraints
import GRAssembly.BoundaryConstraintsJets
import GRAssembly.NativeGluingGaussianCoordinates

/-!
Actual first-order Gaussian evolution. The redundant 96-component matrix
state has a symmetric acceleration on every jet, including incompatible jets.
Symmetry and spatial-jet compatibility are subsequent consequences of the
evolution and initial data. No Gaussian existence premise is introduced here.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.NativeLiterature

open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

abbrev GaussianBase := ℝ × Vec
abbrev GaussianState := (Tensor4 × Tensor4) × (Fin 4 → Tensor4)

def gaussianBaseBasis (a : Fin 4) : GaussianBase :=
  Fin.cases (1, 0) (fun i => (0, unitVector i)) a

def gaussianBulkCoordinates : (ℝ × GaussianBase) →L[ℝ] Bulk :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => bulkPoint z.1 z.2.1 z.2.2
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

def gaussianSplitCoordinates : Bulk →L[ℝ] (ℝ × GaussianBase) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (z 0, (z 1, bulkSpatialCoordinates z))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem gaussianBulkCoordinates_apply (z : ℝ × GaussianBase) :
    gaussianBulkCoordinates z = bulkPoint z.1 z.2.1 z.2.2 := rfl

@[simp] theorem gaussianSplitCoordinates_bulkPoint (r t : ℝ) (x : Vec) :
    gaussianSplitCoordinates (bulkPoint r t x) = (r, (t, x)) := by
  simp [gaussianSplitCoordinates, bulkPoint_radial, bulkPoint_time,
    Assembly.bulkSpatialCoordinates_bulkPoint]

@[simp] theorem gaussianBulkCoordinates_split (z : Bulk) :
    gaussianBulkCoordinates (gaussianSplitCoordinates z) = z :=
  bulkPoint_coordinates z

def gaussianSymmetrize : Tensor4 →L[ℝ] Tensor4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (1 / 2 : ℝ) • (A + A.transpose)
      map_add' := by intros; ext a b; simp; ring
      map_smul' := by intros; ext a b; simp; ring }

@[simp] theorem gaussianSymmetrize_apply (A : Tensor4) (a b : Fin 4) :
    gaussianSymmetrize A a b = (A a b + A b a) / 2 := by
  change (1 / 2 : ℝ) * (A a b + A b a) = _
  ring

theorem gaussianSymmetrize_isSymm (A : Tensor4) :
    (gaussianSymmetrize A).IsSymm := by
  ext a b
  simp only [Matrix.transpose_apply, gaussianSymmetrize_apply]
  ring

theorem gaussianSymmetrize_eq_of_isSymm {A : Tensor4} (hA : A.IsSymm) :
    gaussianSymmetrize A = A := by
  ext a b
  rw [gaussianSymmetrize_apply, hA.apply a b]
  ring

def gaussianStateMetric : GaussianState →L[ℝ] Tensor4 :=
  (ContinuousLinearMap.fst ℝ Tensor4 Tensor4).comp
    (ContinuousLinearMap.fst ℝ (Tensor4 × Tensor4) (Fin 4 → Tensor4))

def gaussianStateVelocity : GaussianState →L[ℝ] Tensor4 :=
  (ContinuousLinearMap.snd ℝ Tensor4 Tensor4).comp
    (ContinuousLinearMap.fst ℝ (Tensor4 × Tensor4) (Fin 4 → Tensor4))

def gaussianStateSpatial (a : Fin 4) : GaussianState →L[ℝ] Tensor4 :=
  (ContinuousLinearMap.proj a).comp
    (ContinuousLinearMap.snd ℝ (Tensor4 × Tensor4) (Fin 4 → Tensor4))

def gaussianInitialState (K : BoundaryTensor) (y : GaussianBase) : GaussianState :=
  ((eta4Matrix, 2 • gaussianSymmetrize (K y.1 y.2)), 0)

theorem gaussianInitialState_analyticAt {K : BoundaryTensor} {y : GaussianBase}
    (hK : AnalyticAt ℝ (fun q : GaussianBase => K q.1 q.2) y) :
    AnalyticAt ℝ (gaussianInitialState K) y := by
  exact (analyticAt_const.prod
    (((gaussianSymmetrize.analyticAt _).comp hK).const_smul 2)).prod analyticAt_const

def gaussianJetMetric (J : CKJet GaussianBase GaussianState) : Tensor4 := J.2.1.1.1
def gaussianJetVelocity (J : CKJet GaussianBase GaussianState) : Tensor4 := J.2.1.1.2
def gaussianJetSpatial (J : CKJet GaussianBase GaussianState) (a : Fin 4) : Tensor4 :=
  J.2.1.2 a
def gaussianJetSecond (J : CKJet GaussianBase GaussianState) (a b : Fin 4) : Tensor4 :=
  (J.2.2 (gaussianBaseBasis a)).2 b

def gaussianJetConnection (J : CKJet GaussianBase GaussianState) (a b c : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin 4,
    (gaussianJetMetric J)⁻¹ a d *
      (gaussianJetSpatial J b d c + gaussianJetSpatial J c d b - gaussianJetSpatial J d b c)

def gaussianJetInverseDerivative (J : CKJet GaussianBase GaussianState)
    (c : Fin 4) : Tensor4 :=
  -((gaussianJetMetric J)⁻¹ * gaussianJetSpatial J c * (gaussianJetMetric J)⁻¹)

def gaussianJetConnectionDerivative (J : CKJet GaussianBase GaussianState)
    (c a b d : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ e : Fin 4,
    gaussianJetInverseDerivative J c a e *
      (gaussianJetSpatial J b e d + gaussianJetSpatial J d e b - gaussianJetSpatial J e b d) +
    (gaussianJetMetric J)⁻¹ a e *
      (gaussianJetSecond J c b e d + gaussianJetSecond J c d e b - gaussianJetSecond J c e b d)

def gaussianJetRicci (J : CKJet GaussianBase GaussianState) : Tensor4 := fun a b =>
  (∑ c : Fin 4,
    gaussianJetConnectionDerivative J c c a b - gaussianJetConnectionDerivative J b c a c) +
  ∑ c : Fin 4, ∑ d : Fin 4,
    gaussianJetConnection J c c d * gaussianJetConnection J d a b -
    gaussianJetConnection J c b d * gaussianJetConnection J d a c

def gaussianJetTrace (J : CKJet GaussianBase GaussianState) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace ((gaussianJetMetric J)⁻¹ * gaussianJetVelocity J)

theorem gaussianJetMetric_analyticAt (J : CKJet GaussianBase GaussianState) :
    AnalyticAt ℝ gaussianJetMetric J := by
  unfold gaussianJetMetric
  fun_prop

theorem gaussianJetVelocity_analyticAt (J : CKJet GaussianBase GaussianState) :
    AnalyticAt ℝ gaussianJetVelocity J := by
  unfold gaussianJetVelocity
  fun_prop

theorem gaussianJetSpatial_analyticAt (J : CKJet GaussianBase GaussianState) (a : Fin 4) :
    AnalyticAt ℝ (fun L => gaussianJetSpatial L a) J := by
  unfold gaussianJetSpatial
  fun_prop

theorem gaussianJetSecond_analyticAt (J : CKJet GaussianBase GaussianState) (a b : Fin 4) :
    AnalyticAt ℝ (fun L => gaussianJetSecond L a b) J := by
  unfold gaussianJetSecond
  fun_prop

theorem gaussianJetInverse_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) :
    AnalyticAt ℝ (fun L => (gaussianJetMetric L)⁻¹) J := by
  have hu : IsUnit (gaussianJetMetric J) :=
    (gaussianJetMetric J).isUnit_iff_isUnit_det.mpr hJ
  have hi : AnalyticAt ℝ (fun A : Tensor4 => A⁻¹) (gaussianJetMetric J) := by
    have he : (fun A : Tensor4 => A⁻¹) = Ring.inverse := by
      funext A
      exact Matrix.nonsing_inv_eq_ringInverse A
    rw [he]
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) hu.unit)
  exact hi.comp (gaussianJetMetric_analyticAt J)

theorem gaussianJetConnection_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) (a b c : Fin 4) :
    AnalyticAt ℝ (fun L => gaussianJetConnection L a b c) J := by
  unfold gaussianJetConnection
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact (Assembly.analyticAt_matrix_entry (gaussianJetInverse_analyticAt hJ) a d).mul
    (((Assembly.analyticAt_matrix_entry (gaussianJetSpatial_analyticAt J b) d c).add
      (Assembly.analyticAt_matrix_entry (gaussianJetSpatial_analyticAt J c) d b)).sub
      (Assembly.analyticAt_matrix_entry (gaussianJetSpatial_analyticAt J d) b c))

theorem gaussianJetInverseDerivative_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) (c : Fin 4) :
    AnalyticAt ℝ (fun L => gaussianJetInverseDerivative L c) J := by
  exact (((gaussianJetInverse_analyticAt hJ).mul
    (gaussianJetSpatial_analyticAt J c)).mul (gaussianJetInverse_analyticAt hJ)).neg

theorem gaussianJetConnectionDerivative_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) (c a b d : Fin 4) :
    AnalyticAt ℝ (fun L => gaussianJetConnectionDerivative L c a b d) J := by
  unfold gaussianJetConnectionDerivative
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro e he
  exact ((Assembly.analyticAt_matrix_entry
    (gaussianJetInverseDerivative_analyticAt hJ c) a e).mul
      (((Assembly.analyticAt_matrix_entry (gaussianJetSpatial_analyticAt J b) e d).add
        (Assembly.analyticAt_matrix_entry (gaussianJetSpatial_analyticAt J d) e b)).sub
        (Assembly.analyticAt_matrix_entry (gaussianJetSpatial_analyticAt J e) b d))).add
    ((Assembly.analyticAt_matrix_entry (gaussianJetInverse_analyticAt hJ) a e).mul
      (((Assembly.analyticAt_matrix_entry (gaussianJetSecond_analyticAt J c b) e d).add
        (Assembly.analyticAt_matrix_entry (gaussianJetSecond_analyticAt J c d) e b)).sub
        (Assembly.analyticAt_matrix_entry (gaussianJetSecond_analyticAt J c e) b d)))

theorem gaussianJetRicci_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) : AnalyticAt ℝ gaussianJetRicci J := by
  apply Assembly.analyticAt_matrix_of_entries
  intro a b
  unfold gaussianJetRicci
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro c hc
    exact (gaussianJetConnectionDerivative_analyticAt hJ c c a b).sub
      (gaussianJetConnectionDerivative_analyticAt hJ b c a c)
  · apply Finset.analyticAt_fun_sum
    intro c hc
    apply Finset.analyticAt_fun_sum
    intro d hd
    exact ((gaussianJetConnection_analyticAt hJ c c d).mul
      (gaussianJetConnection_analyticAt hJ d a b)).sub
      ((gaussianJetConnection_analyticAt hJ c b d).mul
        (gaussianJetConnection_analyticAt hJ d a c))

theorem gaussianJetTrace_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) : AnalyticAt ℝ gaussianJetTrace J := by
  unfold gaussianJetTrace Matrix.trace
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro a ha
  exact Assembly.analyticAt_matrix_entry
    ((gaussianJetInverse_analyticAt hJ).mul (gaussianJetVelocity_analyticAt J)) a a

def gaussianCKRHS : CKRHS GaussianBase GaussianState := fun J =>
  ((gaussianJetVelocity J,
    gaussianSymmetrize (2 • gaussianJetRicci J -
      gaussianJetTrace J • gaussianJetVelocity J +
      gaussianJetVelocity J * (gaussianJetMetric J)⁻¹ * gaussianJetVelocity J)),
    fun a => gaussianStateVelocity (J.2.2 (gaussianBaseBasis a)))

theorem gaussianCKRHS_analyticAt {J : CKJet GaussianBase GaussianState}
    (hJ : IsUnit (gaussianJetMetric J).det) : AnalyticAt ℝ gaussianCKRHS J := by
  have hacc := (gaussianSymmetrize.analyticAt _).comp
    ((((gaussianJetRicci_analyticAt hJ).const_smul 2).sub
      ((gaussianJetTrace_analyticAt hJ).smul (gaussianJetVelocity_analyticAt J))).add
      (((gaussianJetVelocity_analyticAt J).mul (gaussianJetInverse_analyticAt hJ)).mul
        (gaussianJetVelocity_analyticAt J)))
  apply ((gaussianJetVelocity_analyticAt J).prod hacc).prod
  apply AnalyticAt.pi
  intro a
  exact (gaussianStateVelocity.analyticAt _).comp (by fun_prop)

theorem gaussianCKRHS_metric (J : CKJet GaussianBase GaussianState) :
    gaussianStateMetric (gaussianCKRHS J) = gaussianJetVelocity J := rfl

theorem gaussianCKRHS_velocity_symmetric (J : CKJet GaussianBase GaussianState) :
    (gaussianStateVelocity (gaussianCKRHS J)).IsSymm :=
  gaussianSymmetrize_isSymm _

theorem gaussianCKRHS_spatial (J : CKJet GaussianBase GaussianState) (a : Fin 4) :
    gaussianStateSpatial a (gaussianCKRHS J) =
      gaussianStateVelocity (J.2.2 (gaussianBaseBasis a)) := rfl

abbrev GaussianEvolutionStateSolution (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec)
    (U : ℝ × GaussianBase → GaussianState) : Prop :=
  CKLocalSolution gaussianCKRHS (gaussianInitialState K) 0 (t0, x0) U

def gaussianStateSolutionMetric (U : ℝ × GaussianBase → GaussianState) : Bulk → Tensor4 :=
  fun z => gaussianStateMetric (U (gaussianSplitCoordinates z))

def gaussianStateSolutionVelocity (U : ℝ × GaussianBase → GaussianState) : Bulk → Tensor4 :=
  fun z => gaussianStateVelocity (U (gaussianSplitCoordinates z))

def gaussianStateSolutionSpatial (U : ℝ × GaussianBase → GaussianState)
    (a : Fin 4) : Bulk → Tensor4 :=
  fun z => gaussianStateSpatial a (U (gaussianSplitCoordinates z))

theorem gaussianEta_determinant : eta4Matrix.det = -1 := by
  have he : eta4Matrix = Matrix.diagonal lorentzSign4 := by
    ext a b
    simp [eta4Matrix, eta4, Matrix.diagonal_apply]
  rw [he, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ, lorentzSign4]

theorem gaussianEta_isUnit : IsUnit eta4Matrix.det := by
  rw [gaussianEta_determinant]
  exact isUnit_neg_one

theorem gaussianStateSolutionMetric_analyticAt {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    AnalyticAt ℝ (gaussianStateSolutionMetric U) (bulkPoint 0 t0 x0) := by
  exact (gaussianStateMetric.analyticAt _).comp
    (hU.analytic.comp (gaussianSplitCoordinates.analyticAt _))

theorem gaussianStateSolutionVelocity_analyticAt {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    AnalyticAt ℝ (gaussianStateSolutionVelocity U) (bulkPoint 0 t0 x0) := by
  exact (gaussianStateVelocity.analyticAt _).comp
    (hU.analytic.comp (gaussianSplitCoordinates.analyticAt _))

theorem gaussianStateSolutionSpatial_analyticAt {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) (a : Fin 4) :
    AnalyticAt ℝ (gaussianStateSolutionSpatial U a) (bulkPoint 0 t0 x0) := by
  exact ((gaussianStateSpatial a).analyticAt _).comp
    (hU.analytic.comp (gaussianSplitCoordinates.analyticAt _))

theorem gaussianStateSolutionMetric_induced {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ y in 𝓝 (t0, x0), gaussianStateSolutionMetric U (bulkPoint 0 y.1 y.2) = eta4Matrix := by
  filter_upwards [hU.initial] with y hy
  simpa only [gaussianStateSolutionMetric, gaussianSplitCoordinates_bulkPoint,
    hy, gaussianInitialState] using
    (show gaussianStateMetric (gaussianInitialState K y) = eta4Matrix from rfl)

theorem gaussianStateSolutionVelocity_initial {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U)
    (hS : ∀ᶠ y in 𝓝 (t0, x0), (K y.1 y.2).IsSymm) :
    ∀ᶠ y in 𝓝 (t0, x0),
      gaussianStateSolutionVelocity U (bulkPoint 0 y.1 y.2) = 2 • K y.1 y.2 := by
  filter_upwards [hU.initial, hS] with y hy hs
  simp only [gaussianStateSolutionVelocity, gaussianSplitCoordinates_bulkPoint, hy]
  change 2 • gaussianSymmetrize (K y.1 y.2) = 2 • K y.1 y.2
  rw [gaussianSymmetrize_eq_of_isSymm hs]

theorem gaussianStateSolutionMetric_nondegenerate {K : BoundaryTensor} {t0 : ℝ} {x0 : Vec}
    {U : ℝ × GaussianBase → GaussianState}
    (hU : GaussianEvolutionStateSolution K t0 x0 U) :
    ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), IsUnit (gaussianStateSolutionMetric U z).det := by
  have hc : ContinuousAt (fun z => (gaussianStateSolutionMetric U z).det)
      (bulkPoint 0 t0 x0) :=
    Matrix.continuous_det.continuousAt.comp (gaussianStateSolutionMetric_analyticAt hU).continuousAt
  have he := (gaussianStateSolutionMetric_induced hU).self_of_nhds
  have hn : (gaussianStateSolutionMetric U (bulkPoint 0 t0 x0)).det ≠ 0 := by
    rw [he, gaussianEta_determinant]
    norm_num
  exact (hc.eventually_ne hn).mono (fun z hz => isUnit_iff_ne_zero.mpr hz)

/-- Only tangential Einstein equations are part of this evolution germ. -/
structure GaussianEvolutionGerm (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec)
    (h : Bulk → Tensor4) : Prop where
  analytic : AnalyticAt ℝ h (bulkPoint 0 t0 x0)
  symmetric : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), (h z).IsSymm
  nondegenerate : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), IsUnit (h z).det
  induced : ∀ᶠ y in 𝓝 (t0, x0), h (bulkPoint 0 y.1 y.2) = eta4Matrix
  boundary_match : ∀ᶠ y in 𝓝 (t0, x0),
    gaussianSecondForm h (bulkPoint 0 y.1 y.2) = K y.1 y.2
  tangential_vacuum : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), ∀ a b : Fin 4,
    ricci (gaussianMetric h) z a.succ b.succ = 0

end
end NSEGR.NativeLiterature
