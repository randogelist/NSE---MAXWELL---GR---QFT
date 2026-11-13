import GRAdapter.Geometry
import GRAdapter.Fields
import GRAdapter.Algebra

/-!
# Independent boundary reconstruction from the actual metric jet

All components, derivatives, Poisson/Leray expressions and constraints are
concrete. Operator convergence and the Gauss--Codazzi identification are
independent proof obligations; they are not encoded in these definitions.
-/

set_option autoImplicit false

open Set
open scoped BigOperators Matrix.Norms.Frobenius

namespace NSEGR

noncomputable section

abbrev BoundaryTensor := ℝ → Vec → Tensor4

def bulkPoint (r t : ℝ) (x : Vec) : Bulk :=
  WithLp.toLp 2 (Fin.cases r (Fin.cases t (fun i : Fin 3 => x i)))

def boundaryIndex (a : Fin 4) : Fin 5 := a.succ
def spatialIndex4 (i : Fin 3) : Fin 4 := i.succ

@[simp] theorem bulkPoint_radial (r t : ℝ) (x : Vec) :
    bulkPoint r t x 0 = r := by
  simp [bulkPoint, PiLp.toLp_apply]

@[simp] theorem bulkPoint_time (r t : ℝ) (x : Vec) :
    bulkPoint r t x 1 = t := by
  change bulkPoint r t x (0 : Fin 4).succ = t
  simp [bulkPoint, PiLp.toLp_apply]

@[simp] theorem bulkPoint_spatial (r t : ℝ) (x : Vec) (i : Fin 3) :
    bulkPoint r t x i.succ.succ = x i := by
  simp [bulkPoint, PiLp.toLp_apply]

/-- Actual half radial derivative, with the chosen normal +partial_r. -/
def boundaryK (g : Metric) : BoundaryTensor := fun t x a b =>
  (1 / 2 : ℝ) * bulkPartial
    (fun z => g z (boundaryIndex a) (boundaryIndex b)) 0 (bulkPoint 0 t x)

def boundarySpatialTensor (K : BoundaryTensor) (t : ℝ) : TensorField :=
  fun x i j => K t x (spatialIndex4 i) (spatialIndex4 j)

def boundaryBeta (K : BoundaryTensor) : Pressure :=
  fun t x => -(∑ i : Fin 3, K t x (spatialIndex4 i) (spatialIndex4 i))

def boundaryRawVelocity (K : BoundaryTensor) : Velocity :=
  fun t x => WithLp.toLp 2 (fun i : Fin 3 => K t x 0 (spatialIndex4 i))

def boundaryVelocity (K : BoundaryTensor) : Velocity :=
  fun t => leray (boundaryRawVelocity K t)

def boundaryPotential (K : BoundaryTensor) : Pressure :=
  fun t => poissonInverse (fun x => boundaryBeta K t x - scalarMean (boundaryBeta K t))

def boundaryPressure (ρ : ℝ) (K : BoundaryTensor) : Pressure := fun t x =>
  -K t x 0 0 - (2 * ρ + vectorSq3 (fun i => boundaryVelocity K t x i)) / 3 -
    scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t x

def velocityOuter (u : Vec) : Tensor3 := fun i j => u i * u j

/-- The literal STF constitutive tensor. No NSE solution predicate occurs. -/
def boundaryStress (ν : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec) : Tensor3 :=
  tf3 (boundarySpatialTensor K t x + velocityOuter (boundaryVelocity K t x) +
    scalarHessian (boundaryPotential K t) x - ν • strain (boundaryVelocity K t) x)

/-- Tangential derivative in the marked `(t,x1,x2,x3)` coordinates. -/
def boundaryPartial (f : Pressure) (a : Fin 4) (t : ℝ) (x : Vec) : ℝ :=
  Fin.cases (deriv (fun s : ℝ => f s x) t)
    (fun i : Fin 3 => fderiv ℝ (f t) x (unitVector i)) a

def boundaryHessian (f : Pressure) (t : ℝ) (x : Vec) : Tensor4 :=
  fun a b => boundaryPartial (fun s y => boundaryPartial f b s y) a t x

def boundaryHamiltonian (K : BoundaryTensor) (t : ℝ) (x : Vec) : ℝ :=
  lorentzSquare4 (K t x) - (lorentzTrace4 (K t x)) ^ 2

/-- The actual flat-boundary vacuum Codazzi expression
`partial^a (K_ab - kappa eta_ab)`. -/
def boundaryCodazzi (K : BoundaryTensor) (t : ℝ) (x : Vec) (b : Fin 4) : ℝ :=
  ∑ a : Fin 4, lorentzSign4 a *
    boundaryPartial (fun s y => K s y a b - lorentzTrace4 (K s y) * eta4 a b) a t x

theorem boundarySpatialTensor_congr_slice (K L : BoundaryTensor) (t : ℝ)
    (h : K t = L t) : boundarySpatialTensor K t = boundarySpatialTensor L t := by
  funext x i j
  change K t x (spatialIndex4 i) (spatialIndex4 j) =
    L t x (spatialIndex4 i) (spatialIndex4 j)
  rw [h]

theorem boundaryBeta_congr_slice (K L : BoundaryTensor) (t : ℝ)
    (h : K t = L t) : boundaryBeta K t = boundaryBeta L t := by
  funext x
  change -(∑ i : Fin 3, K t x (spatialIndex4 i) (spatialIndex4 i)) =
    -(∑ i : Fin 3, L t x (spatialIndex4 i) (spatialIndex4 i))
  rw [h]

theorem boundaryRawVelocity_congr_slice (K L : BoundaryTensor) (t : ℝ)
    (h : K t = L t) : boundaryRawVelocity K t = boundaryRawVelocity L t := by
  funext x
  change WithLp.toLp 2 (fun i : Fin 3 => K t x 0 (spatialIndex4 i)) =
    WithLp.toLp 2 (fun i : Fin 3 => L t x 0 (spatialIndex4 i))
  rw [h]

theorem boundaryVelocity_congr_slice (K L : BoundaryTensor) (t : ℝ)
    (h : K t = L t) : boundaryVelocity K t = boundaryVelocity L t := by
  change leray (boundaryRawVelocity K t) = leray (boundaryRawVelocity L t)
  exact congrArg leray (boundaryRawVelocity_congr_slice K L t h)

theorem boundaryPotential_congr_slice (K L : BoundaryTensor) (t : ℝ)
    (h : K t = L t) : boundaryPotential K t = boundaryPotential L t := by
  change poissonInverse (fun x => boundaryBeta K t x - scalarMean (boundaryBeta K t)) =
    poissonInverse (fun x => boundaryBeta L t x - scalarMean (boundaryBeta L t))
  rw [boundaryBeta_congr_slice K L t h]

theorem boundaryStress_congr_slice (ν : ℝ) (K L : BoundaryTensor) (t : ℝ)
    (h : K t = L t) : boundaryStress ν K t = boundaryStress ν L t := by
  funext x
  unfold boundaryStress
  rw [boundarySpatialTensor_congr_slice K L t h,
    boundaryVelocity_congr_slice K L t h, boundaryPotential_congr_slice K L t h]

theorem boundaryStress_trace_zero (ν : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec) :
    trace3 (boundaryStress ν K t x) = 0 := by
  exact trace3_tf3 _

theorem boundaryStress_viscosity_difference (ν μ : ℝ) (K : BoundaryTensor)
    (t : ℝ) (x : Vec) (hdiv : divergence (boundaryVelocity K t) x = 0) :
    boundaryStress ν K t x - boundaryStress μ K t x =
      -(ν - μ) • strain (boundaryVelocity K t) x := by
  have hz : trace3 (strain (boundaryVelocity K t) x) = 0 := by
    rw [trace3_eq_matrix_trace, trace_strain, hdiv, mul_zero]
  exact viscosityResidual_difference _ _ hz ν μ

@[simp] theorem boundaryK_constant (M : BulkMatrix) :
    boundaryK (fun _ : Bulk => M) = 0 := by
  funext t x a b
  simp [boundaryK]

@[simp] theorem boundaryK_flat : boundaryK flatMetric = 0 := by
  exact boundaryK_constant eta5

@[simp] theorem boundarySpatialTensor_zero :
    boundarySpatialTensor (0 : BoundaryTensor) = 0 := by
  funext t x i j
  simp [boundarySpatialTensor]

@[simp] theorem boundaryBeta_zero : boundaryBeta (0 : BoundaryTensor) = 0 := by
  funext t x
  simp [boundaryBeta]

@[simp] theorem boundaryRawVelocity_zero :
    boundaryRawVelocity (0 : BoundaryTensor) = 0 := by
  funext t x
  apply PiLp.ext
  intro i
  simp [boundaryRawVelocity, PiLp.toLp_apply]

@[simp] theorem boundaryVelocity_zero : boundaryVelocity (0 : BoundaryTensor) = 0 := by
  funext t x
  simp [boundaryVelocity]

@[simp] theorem boundaryPotential_zero : boundaryPotential (0 : BoundaryTensor) = 0 := by
  funext t x
  simp [boundaryPotential, poissonInverse]

@[simp] theorem velocityOuter_zero : velocityOuter (0 : Vec) = 0 := by
  ext i j
  simp [velocityOuter]

@[simp] theorem boundaryStress_zero (ν : ℝ) : boundaryStress ν (0 : BoundaryTensor) = 0 := by
  funext t x
  simp [boundaryStress]

@[simp] theorem boundaryPartial_const (c : ℝ) (a : Fin 4) (t : ℝ) (x : Vec) :
    boundaryPartial (fun _ _ => c) a t x = 0 := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [boundaryPartial]
  · simp [boundaryPartial]

@[simp] theorem boundaryHessian_const (c : ℝ) (t : ℝ) (x : Vec) :
    boundaryHessian (fun _ _ => c) t x = 0 := by
  ext a b
  simp [boundaryHessian]

@[simp] theorem boundaryHamiltonian_zero :
    boundaryHamiltonian (0 : BoundaryTensor) = 0 := by
  funext t x
  simp [boundaryHamiltonian, lorentzSquare4, lorentzTrace4]

@[simp] theorem boundaryCodazzi_zero : boundaryCodazzi (0 : BoundaryTensor) = 0 := by
  funext t x b
  simp [boundaryCodazzi, lorentzTrace4]

end

end NSEGR
