import ClassicalMechanicsAssembly.PiolaTransport

/-!
# Native determinant transport for a three-dimensional variational ODE

The determinant derivative is obtained from its six actual monomials.
The matrix equation `F' = G * F` gives `(det F)' = trace G * det F`
without an invertibility premise.  Zero trace and `F(0) = I` imply unit
determinant on the entire closed interval, including both endpoints.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open ClassicalMechanics NSEMaxwell.Classical Set
open scoped BigOperators ContDiff Matrix

noncomputable section

/-- The actual determinant chain rule specialized to `F' = G * F`. -/
theorem det_hasDerivWithinAt_mul
    {F : ℝ → StressTensor} {G : StressTensor} {I : Set ℝ} {t : ℝ}
    (hF : HasDerivWithinAt F (G * F t) I t) :
    HasDerivWithinAt (fun s => (F s).det) (G.trace * (F t).det) I t := by
  have hc (i j : Fin 3) :
      HasDerivWithinAt (fun s => F s i j) ((G * F t) i j) I t :=
    hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hF i) j
  have h1 := ((hc 0 0).mul (hc 1 1)).mul (hc 2 2)
  have h2 := ((hc 0 0).mul (hc 1 2)).mul (hc 2 1)
  have h3 := ((hc 0 1).mul (hc 1 0)).mul (hc 2 2)
  have h4 := ((hc 0 1).mul (hc 1 2)).mul (hc 2 0)
  have h5 := ((hc 0 2).mul (hc 1 0)).mul (hc 2 1)
  have h6 := ((hc 0 2).mul (hc 1 1)).mul (hc 2 0)
  have hdet := ((((h1.sub h2).sub h3).add h4).add h5).sub h6
  have hdet' := hdet.congr (f₁ := fun s => (F s).det)
    (fun s _ => Matrix.det_fin_three (F s)) (Matrix.det_fin_three (F t))
  apply hdet'.congr_deriv
  simp only [Pi.mul_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.det_fin_three, Fin.sum_univ_three]
  ring

/-- Traceless matrix evolution gives the actual zero derivative of its determinant. -/
theorem det_hasDerivWithinAt_zero_of_trace_zero
    {F : ℝ → StressTensor} {G : StressTensor} {I : Set ℝ} {t : ℝ}
    (hF : HasDerivWithinAt F (G * F t) I t) (htrace : G.trace = 0) :
    HasDerivWithinAt (fun s => (F s).det) 0 I t := by
  simpa only [htrace, zero_mul] using det_hasDerivWithinAt_mul hF

/-- Determinant conservation on a closed interval from the actual matrix ODE. -/
theorem determinant_eq_initial_of_matrix_ode_trace_zero
    {T : ℝ} (hT : 0 < T) (F G : ℝ → StressTensor)
    (hF : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt F (G t * F t) (Icc (0 : ℝ) T) t)
    (htrace : ∀ t ∈ Icc (0 : ℝ) T, (G t).trace = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, (F t).det = (F 0).det := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun s => (F s).det) 0 (Icc (0 : ℝ) T) t :=
    det_hasDerivWithinAt_zero_of_trace_zero (hF t ht) (htrace t ht)
  have hdiff : DifferentiableOn ℝ (fun s => (F s).det) (Icc (0 : ℝ) T) :=
    fun t ht => (hd t ht).differentiableWithinAt
  apply constant_of_derivWithin_zero hdiff
  intro t ht
  have htc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  exact (hd t htc).derivWithin (uniqueDiffOn_Icc hT t htc)

/-- Unit initial matrix and zero-trace variational evolution preserve determinant one. -/
theorem determinant_one_of_matrix_ode
    {T : ℝ} (hT : 0 < T) (F G : ℝ → StressTensor)
    (hF : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt F (G t * F t) (Icc (0 : ℝ) T) t)
    (htrace : ∀ t ∈ Icc (0 : ℝ) T, (G t).trace = 0)
    (hF0 : F 0 = 1) :
    ∀ t ∈ Icc (0 : ℝ) T, (F t).det = 1 := by
  intro t ht
  rw [determinant_eq_initial_of_matrix_ode_trace_zero hT F G hF htrace t ht,
    hF0, Matrix.det_one]

/-- The trace of the native velocity-gradient matrix is its native divergence. -/
theorem trace_materialGradientMatrix (v : Field) (x : Vec) :
    (materialGradientMatrix v x).trace = NSEMaxwell.Classical.divergence v x := by
  rfl

/-- The native derivative of the identity configuration is the identity matrix. -/
theorem materialGradientMatrix_id (a : Vec) :
    materialGradientMatrix (fun x : Vec => x) a = 1 := by
  ext i j
  simp [materialGradientMatrix, coordinateDerivative, unitVector,
    Matrix.one_apply, EuclideanSpace.single, PiLp.single_apply, eq_comm]

/-- E14: unit Jacobian from the supplied actual variational ODE and incompressibility. -/
theorem FLOW_JACOBIAN_ONE_OF_VARIATIONAL_ODE
    {T : ℝ} (hT : 0 < T) {u η : Velocity}
    (hη0 : η 0 = fun a : Vec => a)
    (hvar : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      HasDerivWithinAt (fun s => deformationGradient η s a)
        (materialGradientMatrix (u t) (η t a) * deformationGradient η t a)
        (Icc (0 : ℝ) T) t)
    (hdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      NSEMaxwell.Classical.divergence (u t) x = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, (deformationGradient η t a).det = 1 := by
  intro t ht a
  apply determinant_one_of_matrix_ode hT
    (fun s => deformationGradient η s a)
    (fun s => materialGradientMatrix (u s) (η s a))
    (fun s hs => hvar s hs a) _ _ t ht
  · intro s hs
    rw [trace_materialGradientMatrix]
    exact hdiv s hs (η s a)
  · change materialGradientMatrix (η 0) a = 1
    rw [hη0, materialGradientMatrix_id]

end

end ClassicalMechanicsAssembly
