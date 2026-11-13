import GRAdapter.Boundary

/-!
# Concrete source and scalar Hamiltonian completion formulas

The source is the actual velocity/pressure/strain tensor. The scalar
correction uses actual first and second derivatives. No conservation,
analytic existence, constraint propagation, or metric realization theorem
is inferred from these definitions.
-/

set_option autoImplicit false

namespace NSEGR

noncomputable section

/-- The actual contravariant NSE source S^(00)=rho, S^(0i)=u_i. -/
def conservedSourceUpper (ν ρ : ℝ) (u : Velocity) (p : Pressure) : BoundaryTensor :=
  fun t x => boundaryBlock ρ (fun i => u t x i)
    (fun i j => u t x i * u t x j + p t x * identity3 i j - ν * strain (u t) x i j)

/-- The contravariant scalar correction C^(ab)[psi]. -/
def scalarCompletionUpper (ψ : Pressure) : BoundaryTensor :=
  fun t x => boundaryBlock (scalarLaplacian (ψ t) x)
    (fun i => -(gradient (scalarLocalTimeDerivative ψ t) x i))
    (fun i j => scalarHessian (ψ t) x i j +
      (scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x -
        scalarLaplacian (ψ t) x) * identity3 i j)

/-- Lower both indices with the actual boundary metric diag(-1,1,1,1). -/
def lowerTensor4 (T : Tensor4) : Tensor4 :=
  fun a b => lorentzSign4 a * lorentzSign4 b * T a b

/-- Actual covariant K supplied by the normalized scalar completion. -/
def completedBoundary (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure) : BoundaryTensor :=
  fun t x => traceReverse4
    (lowerTensor4 (conservedSourceUpper ν ρ u p t x + scalarCompletionUpper ψ t x))

@[simp] theorem lorentzSign4_mul_self (a : Fin 4) :
    lorentzSign4 a * lorentzSign4 a = 1 := by
  by_cases h : a = 0 <;> simp [lorentzSign4, h]

theorem lowerTensor4_involutive (T : Tensor4) : lowerTensor4 (lowerTensor4 T) = T := by
  ext a b
  change lorentzSign4 a * lorentzSign4 b *
    (lorentzSign4 a * lorentzSign4 b * T a b) = T a b
  calc
    _ = (lorentzSign4 a * lorentzSign4 a) *
      (lorentzSign4 b * lorentzSign4 b) * T a b := by ring
    _ = T a b := by simp

theorem lowerTensor4_add (T U : Tensor4) :
    lowerTensor4 (T + U) = lowerTensor4 T + lowerTensor4 U := by
  ext a b
  simp [lowerTensor4] <;> ring

@[simp] theorem lowerTensor4_time_time (T : Tensor4) :
    lowerTensor4 T 0 0 = T 0 0 := by
  simp [lowerTensor4, lorentzSign4]

@[simp] theorem lowerTensor4_time_space (T : Tensor4) (i : Fin 3) :
    lowerTensor4 T 0 i.succ = -T 0 i.succ := by
  simp [lowerTensor4, lorentzSign4]

@[simp] theorem lowerTensor4_space_space (T : Tensor4) (i j : Fin 3) :
    lowerTensor4 T i.succ j.succ = T i.succ j.succ := by
  simp [lowerTensor4, lorentzSign4]

@[simp] theorem conservedSourceUpper_time_time (ν ρ : ℝ) (u : Velocity)
    (p : Pressure) (t : ℝ) (x : Vec) :
    conservedSourceUpper ν ρ u p t x 0 0 = ρ := rfl

@[simp] theorem conservedSourceUpper_time_space (ν ρ : ℝ) (u : Velocity)
    (p : Pressure) (t : ℝ) (x : Vec) (i : Fin 3) :
    conservedSourceUpper ν ρ u p t x 0 i.succ = u t x i := rfl

@[simp] theorem conservedSourceUpper_space_space (ν ρ : ℝ) (u : Velocity)
    (p : Pressure) (t : ℝ) (x : Vec) (i j : Fin 3) :
    conservedSourceUpper ν ρ u p t x i.succ j.succ =
      u t x i * u t x j + p t x * identity3 i j - ν * strain (u t) x i j := rfl

@[simp] theorem scalarCompletionUpper_time_time (ψ : Pressure) (t : ℝ) (x : Vec) :
    scalarCompletionUpper ψ t x 0 0 = scalarLaplacian (ψ t) x := rfl

@[simp] theorem scalarCompletionUpper_time_space (ψ : Pressure) (t : ℝ) (x : Vec)
    (i : Fin 3) : scalarCompletionUpper ψ t x 0 i.succ =
      -(gradient (scalarLocalTimeDerivative ψ t) x i) := rfl

@[simp] theorem scalarCompletionUpper_space_space (ψ : Pressure) (t : ℝ) (x : Vec)
    (i j : Fin 3) : scalarCompletionUpper ψ t x i.succ j.succ =
      scalarHessian (ψ t) x i j +
        (scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x -
          scalarLaplacian (ψ t) x) * identity3 i j := rfl

theorem completedBoundary_trace_recovery (ν ρ : ℝ) (u : Velocity) (p ψ : Pressure)
    (t : ℝ) (x : Vec) :
    traceRecover4 (completedBoundary ν ρ u p ψ t x) =
      lowerTensor4 (conservedSourceUpper ν ρ u p t x + scalarCompletionUpper ψ t x) := by
  exact traceRecover4_traceReverse4 _

theorem completedBoundary_hamiltonian_identity (ν ρ : ℝ) (u : Velocity)
    (p ψ : Pressure) (t : ℝ) (x : Vec) :
    boundaryHamiltonian (completedBoundary ν ρ u p ψ) t x =
      let B := lowerTensor4
        (conservedSourceUpper ν ρ u p t x + scalarCompletionUpper ψ t x)
      lorentzSquare4 B - (lorentzTrace4 B) ^ 2 / 3 := by
  exact traceReverse4_hamiltonian _

end

end NSEGR
