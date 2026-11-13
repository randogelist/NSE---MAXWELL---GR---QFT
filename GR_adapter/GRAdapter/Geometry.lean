import Mathlib

/-!
# Native marked five-dimensional Lorentzian coordinate geometry

The coordinates are `(r,t,x1,x2,x3)`. Derivatives below are the actual
Fréchet derivatives of the supplied metric coefficients. The inverse is
the matrix inverse; `LorentzianAt` supplies its nondegeneracy premise.

The flat witness certifies the native geometric semantics. It does not
satisfy the nonzero-rho constitutive sector merely by being Ricci-flat.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace NSEGR

noncomputable section

abbrev Bulk := EuclideanSpace ℝ (Fin 5)
abbrev BulkMatrix := Matrix (Fin 5) (Fin 5) ℝ
abbrev Metric := Bulk → BulkMatrix

/-- Coordinate direction; index `0` is radial and index `1` is time. -/
def bulkBasis (i : Fin 5) : Bulk :=
  EuclideanSpace.single i (1 : ℝ)

/-- Actual coordinate derivative, not an uninterpreted differential operator. -/
def bulkPartial (f : Bulk → ℝ) (i : Fin 5) (z : Bulk) : ℝ :=
  fderiv ℝ f z (bulkBasis i)

/-- One negative time direction and four positive directions. -/
def eta5 : BulkMatrix :=
  Matrix.diagonal (fun i : Fin 5 => if i = 1 then (-1 : ℝ) else 1)

def flatMetric : Metric := fun _ => eta5

def inverseMetric (g : Metric) : Metric := fun z => (g z)⁻¹

/-- The upper Christoffel index is `a`: `christoffel g z a b c = Γ^a_bc`. -/
def christoffel (g : Metric) (z : Bulk) (a b c : Fin 5) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin 5, inverseMetric g z a d *
    (bulkPartial (fun y => g y d c) b z +
      bulkPartial (fun y => g y d b) c z -
      bulkPartial (fun y => g y b c) d z)

/-- Coordinate Ricci tensor with the convention used by the Gaussian
radial equation in the B-tier derivation. -/
def ricci (g : Metric) : Metric := fun z a b =>
  (∑ c : Fin 5,
    bulkPartial (fun y => christoffel g y c a b) c z -
      bulkPartial (fun y => christoffel g y c a c) b z) +
  ∑ c : Fin 5, ∑ d : Fin 5,
    christoffel g z c c d * christoffel g z d a b -
      christoffel g z c b d * christoffel g z d a c

def scalarCurvature (g : Metric) (z : Bulk) : ℝ :=
  ∑ a : Fin 5, ∑ b : Fin 5, inverseMetric g z a b * ricci g z a b

def einstein (g : Metric) : Metric := fun z a b =>
  ricci g z a b - (1 / 2 : ℝ) * scalarCurvature g z * g z a b

/-- Actual Lorentzian inertia: an invertible real change of basis from eta5.
This is an independent metric predicate, not a proposition supplied by a caller. -/
def LorentzianAt (g : Metric) (z : Bulk) : Prop :=
  ∃ C : BulkMatrix, IsUnit C.det ∧ g z = C.transpose * eta5 * C

def VacuumOn (g : Metric) (U : Set Bulk) : Prop :=
  ∀ z ∈ U, ricci g z = 0

def EinsteinVacuumOn (g : Metric) (U : Set Bulk) : Prop :=
  ∀ z ∈ U, einstein g z = 0

@[simp]
theorem bulkPartial_const (c : ℝ) (i : Fin 5) (z : Bulk) :
    bulkPartial (fun _ => c) i z = 0 := by
  simp [bulkPartial]

theorem eta5_symmetric : eta5.IsSymm := by
  exact Matrix.isSymm_diagonal _

@[simp]
theorem eta5_transpose : eta5.transpose = eta5 :=
  eta5_symmetric

@[simp]
theorem eta5_det : eta5.det = -1 := by
  norm_num [eta5, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem lorentzianAt_symmetric {g : Metric} {z : Bulk}
    (h : LorentzianAt g z) : (g z).IsSymm := by
  rcases h with ⟨C, hC, hmetric⟩
  rw [hmetric]
  change (C.transpose * eta5 * C).transpose = C.transpose * eta5 * C
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem lorentzianAt_det_neg {g : Metric} {z : Bulk}
    (h : LorentzianAt g z) : (g z).det < 0 := by
  rcases h with ⟨C, hC, hmetric⟩
  have hdet : C.det ≠ 0 := hC.ne_zero
  rw [hmetric, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, eta5_det]
  nlinarith [sq_pos_of_ne_zero hdet]

theorem lorentzianAt_nondegenerate {g : Metric} {z : Bulk}
    (h : LorentzianAt g z) : (g z).det ≠ 0 :=
  ne_of_lt (lorentzianAt_det_neg h)

@[simp]
theorem christoffel_constant (M : BulkMatrix) (z : Bulk) (a b c : Fin 5) :
    christoffel (fun _ => M) z a b c = 0 := by
  simp [christoffel]

@[simp]
theorem ricci_constant (M : BulkMatrix) (z : Bulk) :
    ricci (fun _ => M) z = 0 := by
  ext a b
  simp [ricci]

@[simp]
theorem scalarCurvature_constant (M : BulkMatrix) (z : Bulk) :
    scalarCurvature (fun _ => M) z = 0 := by
  simp [scalarCurvature]

@[simp]
theorem einstein_constant (M : BulkMatrix) (z : Bulk) :
    einstein (fun _ => M) z = 0 := by
  ext a b
  simp [einstein]

theorem constant_vacuumOn (M : BulkMatrix) (U : Set Bulk) :
    VacuumOn (fun _ => M) U := by
  intro z hz
  exact ricci_constant M z

theorem vacuumOn_mono {g : Metric} {U V : Set Bulk}
    (h : VacuumOn g U) (hVU : V ⊆ U) : VacuumOn g V := by
  intro z hz
  exact h z (hVU hz)

theorem vacuumOn_implies_einsteinVacuumOn {g : Metric} {U : Set Bulk}
    (h : VacuumOn g U) : EinsteinVacuumOn g U := by
  intro z hz
  have hRic : ricci g z = 0 := h z hz
  have hScalar : scalarCurvature g z = 0 := by
    simp [scalarCurvature, hRic]
  ext a b
  simp [einstein, hRic, hScalar]

theorem flatMetric_lorentzian (z : Bulk) : LorentzianAt flatMetric z := by
  refine ⟨1, ?_, ?_⟩
  · simp
  · simp [flatMetric]

theorem flatMetric_symmetric (z : Bulk) : (flatMetric z).IsSymm :=
  eta5_symmetric

@[simp]
theorem flatMetric_det (z : Bulk) : (flatMetric z).det = -1 := by
  exact eta5_det

theorem flatMetric_nondegenerate (z : Bulk) : (flatMetric z).det ≠ 0 :=
  lorentzianAt_nondegenerate (flatMetric_lorentzian z)

@[simp]
theorem flatMetric_christoffel (z : Bulk) (a b c : Fin 5) :
    christoffel flatMetric z a b c = 0 := by
  exact christoffel_constant eta5 z a b c

@[simp]
theorem flatMetric_ricci (z : Bulk) : ricci flatMetric z = 0 := by
  exact ricci_constant eta5 z

@[simp]
theorem flatMetric_scalarCurvature (z : Bulk) : scalarCurvature flatMetric z = 0 := by
  exact scalarCurvature_constant eta5 z

@[simp]
theorem flatMetric_einstein (z : Bulk) : einstein flatMetric z = 0 := by
  exact einstein_constant eta5 z

theorem flatMetric_vacuumOn (U : Set Bulk) : VacuumOn flatMetric U := by
  exact constant_vacuumOn eta5 U

theorem flatMetric_einsteinVacuumOn (U : Set Bulk) : EinsteinVacuumOn flatMetric U :=
  vacuumOn_implies_einsteinVacuumOn (flatMetric_vacuumOn U)

theorem flatMetric_analyticOnNhd (U : Set Bulk) : AnalyticOnNhd ℝ flatMetric U := by
  exact analyticOnNhd_const

/-- A concrete native analytic Lorentzian vacuum inhabitant on any chosen domain.
No constitutive admission or nonzero-rho normalization is concluded. -/
theorem native_flat_vacuum (U : Set Bulk) :
    AnalyticOnNhd ℝ flatMetric U ∧
      (∀ z ∈ U, LorentzianAt flatMetric z) ∧ VacuumOn flatMetric U := by
  exact ⟨flatMetric_analyticOnNhd U,
    fun z _ => flatMetric_lorentzian z, flatMetric_vacuumOn U⟩

end

end NSEGR
