import Mathlib

/-!
Finite tensor identities for the normalized timelike GR boundary.

Every object below is a concrete finite real matrix. These identities prove
neither a Cauchy--Kowalevski theorem nor the geometric Gauss--Codazzi theorem.
They are the exact algebraic edges used after those independently stated
analytic/geometric obligations have been established.
-/

set_option autoImplicit false

open scoped BigOperators

namespace NSEGR

noncomputable section

abbrev Tensor3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Tensor4 := Matrix (Fin 4) (Fin 4) ℝ

def trace3 (A : Tensor3) : ℝ := A 0 0 + A 1 1 + A 2 2

def identity3 (i j : Fin 3) : ℝ := if i = j then 1 else 0

def tf3 (A : Tensor3) : Tensor3 :=
  fun i j => A i j - (trace3 A / 3) * identity3 i j

def frobeniusSq3 (A : Tensor3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (A i j) ^ 2

def vectorSq3 (u : Fin 3 → ℝ) : ℝ := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2

@[simp] theorem identity3_diag (i : Fin 3) : identity3 i i = 1 := by
  simp [identity3]

theorem trace3_eq_matrix_trace (A : Tensor3) : trace3 A = Matrix.trace A := by
  simp [trace3, Matrix.trace, Fin.sum_univ_succ] <;> ring

@[simp] theorem trace3_zero : trace3 0 = 0 := by
  simp [trace3]

@[simp] theorem trace3_add (A B : Tensor3) : trace3 (A + B) = trace3 A + trace3 B := by
  simp [trace3, smul_eq_mul] <;> ring

@[simp] theorem trace3_sub (A B : Tensor3) : trace3 (A - B) = trace3 A - trace3 B := by
  simp [trace3, smul_eq_mul] <;> ring

@[simp] theorem trace3_smul (a : ℝ) (A : Tensor3) : trace3 (a • A) = a * trace3 A := by
  simp [trace3, smul_eq_mul] <;> ring

@[simp] theorem trace3_tf3 (A : Tensor3) : trace3 (tf3 A) = 0 := by
  simp [trace3, tf3] <;> ring

theorem tf3_eq_self_of_trace_zero (A : Tensor3) (hA : trace3 A = 0) : tf3 A = A := by
  ext i j
  simp [tf3, hA]

@[simp] theorem tf3_zero : tf3 0 = 0 := by
  exact tf3_eq_self_of_trace_zero 0 trace3_zero

@[simp] theorem tf3_idempotent (A : Tensor3) : tf3 (tf3 A) = tf3 A := by
  exact tf3_eq_self_of_trace_zero (tf3 A) (trace3_tf3 A)

theorem tf3_add (A B : Tensor3) : tf3 (A + B) = tf3 A + tf3 B := by
  ext i j
  simp [tf3, smul_eq_mul] <;> ring

theorem tf3_sub (A B : Tensor3) : tf3 (A - B) = tf3 A - tf3 B := by
  ext i j
  simp [tf3, smul_eq_mul] <;> ring

theorem tf3_smul (a : ℝ) (A : Tensor3) : tf3 (a • A) = a • tf3 A := by
  ext i j
  simp [tf3, smul_eq_mul] <;> ring

theorem tf3_symmetric (A : Tensor3) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, tf3 A i j = tf3 A j i := by
  intro i j
  simp only [tf3, hA i j]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [identity3, hij, Ne.symm hij]

theorem tf3_eq_zero_iff (A : Tensor3) :
    tf3 A = 0 ↔ ∀ i j, A i j = (trace3 A / 3) * identity3 i j := by
  constructor
  · intro h i j
    have hij : A i j - (trace3 A / 3) * identity3 i j = 0 := by
      simpa [tf3] using congrArg (fun M : Tensor3 => M i j) h
    exact sub_eq_zero.mp hij
  · intro h
    ext i j
    change A i j - (trace3 A / 3) * identity3 i j = 0
    rw [h i j, sub_self]

theorem frobeniusSq3_nonneg (A : Tensor3) : 0 ≤ frobeniusSq3 A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)

theorem vectorSq3_nonneg (u : Fin 3 → ℝ) : 0 ≤ vectorSq3 u := by
  dsimp [vectorSq3]
  positivity

/-- The actual trace-free constitutive residual at a trial viscosity. -/
def viscosityResidual (A Z : Tensor3) (nu : ℝ) : Tensor3 := tf3 (A - nu • Z)

theorem viscosityResidual_affine (A Z : Tensor3) (hZ : trace3 Z = 0) (nu : ℝ) :
    viscosityResidual A Z nu = tf3 A - nu • Z := by
  rw [viscosityResidual, tf3_sub, tf3_smul, tf3_eq_self_of_trace_zero Z hZ]

theorem viscosityResidual_difference (A Z : Tensor3) (hZ : trace3 Z = 0)
    (nu mu : ℝ) :
    viscosityResidual A Z nu - viscosityResidual A Z mu = -(nu - mu) • Z := by
  rw [viscosityResidual_affine A Z hZ nu, viscosityResidual_affine A Z hZ mu]
  ext i j
  simp [smul_eq_mul] <;> ring

def lorentzSign4 (a : Fin 4) : ℝ := if a = 0 then -1 else 1

def eta4 (a b : Fin 4) : ℝ := if a = b then lorentzSign4 a else 0

def lorentzTrace4 (B : Tensor4) : ℝ := -B 0 0 + B 1 1 + B 2 2 + B 3 3

/-- Both tensor indices are raised by diag(-1,1,1,1). -/
def lorentzSquare4 (B : Tensor4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, lorentzSign4 a * lorentzSign4 b * (B a b) ^ 2

/-- K = (tr_eta B)/3 eta - B, with B in covariant components. -/
def traceReverse4 (B : Tensor4) : Tensor4 :=
  fun a b => (lorentzTrace4 B / 3) * eta4 a b - B a b

def traceRecover4 (K : Tensor4) : Tensor4 :=
  fun a b => lorentzTrace4 K * eta4 a b - K a b

theorem lorentzTrace4_traceReverse4 (B : Tensor4) :
    lorentzTrace4 (traceReverse4 B) = lorentzTrace4 B / 3 := by
  simp [lorentzTrace4, traceReverse4, eta4, lorentzSign4] <;> ring

theorem lorentzTrace4_traceRecover4 (K : Tensor4) :
    lorentzTrace4 (traceRecover4 K) = 3 * lorentzTrace4 K := by
  simp [lorentzTrace4, traceRecover4, eta4, lorentzSign4] <;> ring

theorem traceRecover4_traceReverse4 (B : Tensor4) :
    traceRecover4 (traceReverse4 B) = B := by
  ext a b
  simp only [traceRecover4, lorentzTrace4_traceReverse4, traceReverse4] <;> ring

theorem traceReverse4_traceRecover4 (K : Tensor4) :
    traceReverse4 (traceRecover4 K) = K := by
  ext a b
  simp only [traceReverse4, lorentzTrace4_traceRecover4, traceRecover4] <;> ring

/-- Exact signed Hamiltonian algebra; no geometric constraint is assumed. -/
theorem traceReverse4_hamiltonian (B : Tensor4) :
    lorentzSquare4 (traceReverse4 B) - (lorentzTrace4 (traceReverse4 B)) ^ 2 =
      lorentzSquare4 B - (lorentzTrace4 B) ^ 2 / 3 := by
  rw [lorentzTrace4_traceReverse4]
  simp [lorentzSquare4, Fin.sum_univ_succ, traceReverse4, lorentzTrace4,
    eta4, lorentzSign4] <;> ring

/-- Covariant symmetric time/space block (the spatial block may be arbitrary). -/
def boundaryBlock (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3) : Tensor4 :=
  fun a b =>
    Fin.cases (Fin.cases k (fun j => u j) b)
      (fun i => Fin.cases (u i) (fun j => A i j) b) a

@[simp] theorem boundaryBlock_time_time (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3) :
    boundaryBlock k u A 0 0 = k := rfl

@[simp] theorem boundaryBlock_time_space (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3)
    (i : Fin 3) : boundaryBlock k u A 0 i.succ = u i := rfl

@[simp] theorem boundaryBlock_space_time (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3)
    (i : Fin 3) : boundaryBlock k u A i.succ 0 = u i := rfl

@[simp] theorem boundaryBlock_space_space (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3)
    (i j : Fin 3) : boundaryBlock k u A i.succ j.succ = A i j := rfl

theorem lorentzTrace4_boundaryBlock (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3) :
    lorentzTrace4 (boundaryBlock k u A) = -k + trace3 A := by
  simp [lorentzTrace4, boundaryBlock, trace3] <;> ring

theorem lorentzSquare4_boundaryBlock (k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3) :
    lorentzSquare4 (boundaryBlock k u A) =
      k ^ 2 - 2 * vectorSq3 u + frobeniusSq3 A := by
  simp [lorentzSquare4, boundaryBlock, lorentzSign4, frobeniusSq3,
    vectorSq3, Fin.sum_univ_succ] <;> ring

theorem boundaryBlock_hamiltonian (rho k : ℝ) (u : Fin 3 → ℝ) (A : Tensor3)
    (hA : trace3 A = -rho) :
    lorentzSquare4 (boundaryBlock k u A) - (lorentzTrace4 (boundaryBlock k u A)) ^ 2 =
      frobeniusSq3 A - 2 * vectorSq3 u - rho ^ 2 - 2 * rho * k := by
  rw [lorentzSquare4_boundaryBlock, lorentzTrace4_boundaryBlock, hA] <;> ring

def initialSpatial (rho nu : ℝ) (u : Fin 3 → ℝ) (Z : Tensor3) : Tensor3 :=
  fun i j => ((vectorSq3 u - rho) / 3) * identity3 i j - u i * u j + nu * Z i j

theorem trace3_initialSpatial (rho nu : ℝ) (u : Fin 3 → ℝ) (Z : Tensor3)
    (hZ : trace3 Z = 0) : trace3 (initialSpatial rho nu u Z) = -rho := by
  calc
    trace3 (initialSpatial rho nu u Z) = -rho + nu * trace3 Z := by
      simp [trace3, initialSpatial, vectorSq3] <;> ring
    _ = -rho := by rw [hZ]; ring

def initialTimeTime (rho : ℝ) (u : Fin 3 → ℝ) (A : Tensor3) : ℝ :=
  (frobeniusSq3 A - 2 * vectorSq3 u - rho ^ 2) / (2 * rho)

theorem boundaryBlock_hamiltonian_zero_iff (rho k : ℝ) (u : Fin 3 → ℝ)
    (A : Tensor3) (hrho : rho ≠ 0) (hA : trace3 A = -rho) :
    lorentzSquare4 (boundaryBlock k u A) - (lorentzTrace4 (boundaryBlock k u A)) ^ 2 = 0
      ↔ k = initialTimeTime rho u A := by
  rw [boundaryBlock_hamiltonian rho k u A hA]
  unfold initialTimeTime
  constructor
  · intro h
    apply (eq_div_iff (mul_ne_zero (by norm_num) hrho)).2
    nlinarith
  · intro h
    rw [h]
    field_simp [hrho] <;> ring

theorem initialTimeTime_solves_hamiltonian (rho : ℝ) (u : Fin 3 → ℝ)
    (A : Tensor3) (hrho : rho ≠ 0) (hA : trace3 A = -rho) :
    lorentzSquare4 (boundaryBlock (initialTimeTime rho u A) u A) -
      (lorentzTrace4 (boundaryBlock (initialTimeTime rho u A) u A)) ^ 2 = 0 := by
  exact (boundaryBlock_hamiltonian_zero_iff rho (initialTimeTime rho u A) u A hrho hA).2 rfl

theorem initial_boundary_hamiltonian (rho nu : ℝ) (u : Fin 3 → ℝ)
    (Z : Tensor3) (hrho : rho ≠ 0) (hZ : trace3 Z = 0) :
    let A := initialSpatial rho nu u Z
    lorentzSquare4 (boundaryBlock (initialTimeTime rho u A) u A) -
      (lorentzTrace4 (boundaryBlock (initialTimeTime rho u A) u A)) ^ 2 = 0 := by
  dsimp only
  exact initialTimeTime_solves_hamiltonian rho u (initialSpatial rho nu u Z) hrho
    (trace3_initialSpatial rho nu u Z hZ)

end

end NSEGR
