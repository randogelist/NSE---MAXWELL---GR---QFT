import GRAdapter.CompletionSource

/-!
# Exact native reconstruction algebra

The Poisson/Leray and geometric differential identities remain explicit
hypotheses. The conclusions below are derived from the actual tensors and
operators: no independent source tensor or desired reconstruction equality
is supplied as a hypothesis.
-/

set_option autoImplicit false

open scoped BigOperators

namespace NSEGR
noncomputable section

/-- The diagonal Hessian sum is the actual scalar Laplacian, by definition. -/
theorem reconstruction_trace_scalarHessian (f : ScalarField) (x : Vec) :
    trace3 (scalarHessian f x) = scalarLaplacian f x := by
  rw [trace3_eq_matrix_trace]
  rfl

theorem reconstruction_trace_velocityOuter (v : Vec) :
    trace3 (velocityOuter v) = vectorSq3 (fun i => v i) := by
  simp only [trace3, velocityOuter, vectorSq3]
  ring

theorem reconstruction_trace_boundarySpatial (K : BoundaryTensor) (t : ℝ) (x : Vec) :
    trace3 (boundarySpatialTensor K t x) = -boundaryBeta K t x := by
  rw [trace3_eq_matrix_trace]
  change (∑ i : Fin 3, K t x (spatialIndex4 i) (spatialIndex4 i)) =
    -(-(∑ i : Fin 3, K t x (spatialIndex4 i) (spatialIndex4 i)))
  ring

theorem reconstruction_lorentzTrace_boundary (K : BoundaryTensor) (t : ℝ) (x : Vec) :
    lorentzTrace4 (K t x) = -K t x 0 0 - boundaryBeta K t x := by
  have h := reconstruction_trace_boundarySpatial K t x
  change K t x 1 1 + K t x 2 2 + K t x 3 3 = -boundaryBeta K t x at h
  change -K t x 0 0 + K t x 1 1 + K t x 2 2 + K t x 3 3 =
    -K t x 0 0 - boundaryBeta K t x
  linarith

theorem reconstruction_eta4_spatial (i j : Fin 3) :
    eta4 i.succ j.succ = identity3 i j := by
  simp [eta4, lorentzSign4, identity3]

/-- The trace cancellation only needs the two pointwise operator identities. -/
theorem boundaryPreStress_trace (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hdiv : divergence (boundaryVelocity K t) x = 0)
    (hΔ : scalarLaplacian (boundaryPotential K t) x = boundaryBeta K t x - ρ) :
    trace3 (boundarySpatialTensor K t x + velocityOuter (boundaryVelocity K t x) +
      scalarHessian (boundaryPotential K t) x - ν • strain (boundaryVelocity K t) x) =
      vectorSq3 (fun i => boundaryVelocity K t x i) - ρ := by
  rw [trace3_sub, trace3_add, trace3_add,
    reconstruction_trace_boundarySpatial, reconstruction_trace_velocityOuter,
    reconstruction_trace_scalarHessian, trace3_smul,
    trace3_eq_matrix_trace (strain (boundaryVelocity K t) x), trace_strain, hdiv, hΔ]
  ring

/-- The actual STF admission determines every spatial component. -/
theorem boundarySpatial_eq_of_stress_zero (ν ρ : ℝ) (K : BoundaryTensor)
    (t : ℝ) (x : Vec)
    (hdiv : divergence (boundaryVelocity K t) x = 0)
    (hΔ : scalarLaplacian (boundaryPotential K t) x = boundaryBeta K t x - ρ)
    (hF : boundaryStress ν K t x = 0) (i j : Fin 3) :
    K t x i.succ j.succ =
      ((vectorSq3 (fun l => boundaryVelocity K t x l) - ρ) / 3) * identity3 i j -
        boundaryVelocity K t x i * boundaryVelocity K t x j +
        ν * strain (boundaryVelocity K t) x i j -
        scalarHessian (boundaryPotential K t) x i j := by
  let T : Tensor3 := boundarySpatialTensor K t x +
    velocityOuter (boundaryVelocity K t x) + scalarHessian (boundaryPotential K t) x -
      ν • strain (boundaryVelocity K t) x
  have htr : trace3 T = vectorSq3 (fun l => boundaryVelocity K t x l) - ρ :=
    boundaryPreStress_trace ν ρ K t x hdiv hΔ
  have hzero : tf3 T = 0 := hF
  have hij := (tf3_eq_zero_iff T).mp hzero i j
  rw [htr] at hij
  change K t x i.succ j.succ +
    boundaryVelocity K t x i * boundaryVelocity K t x j +
    scalarHessian (boundaryPotential K t) x i j -
    ν * strain (boundaryVelocity K t) x i j =
      ((vectorSq3 (fun l => boundaryVelocity K t x l) - ρ) / 3) * identity3 i j at hij
  linarith

/-- Full native tensor recovery. The remaining assumptions are symmetry,
solenoidality, the scalar Poisson equation and the raw/decoded Hodge identity.
No scalar CK or radial extension theorem is needed for this algebraic edge. -/
theorem boundary_eq_completedBoundary_of_zero_stress
    (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hsym : (K t x).IsSymm)
    (hdiv : divergence (boundaryVelocity K t) x = 0)
    (hΔ : scalarLaplacian (boundaryPotential K t) x = boundaryBeta K t x - ρ)
    (hraw : boundaryRawVelocity K t x = boundaryVelocity K t x -
      gradient (scalarLocalTimeDerivative (boundaryPotential K) t) x)
    (hF : boundaryStress ν K t x = 0) :
    K t x = completedBoundary ν ρ (boundaryVelocity K)
      (boundaryPressure ρ K) (boundaryPotential K) t x := by
  have hw (i : Fin 3) : K t x 0 i.succ = boundaryVelocity K t x i -
      gradient (scalarLocalTimeDerivative (boundaryPotential K) t) x i := by
    simpa only [boundaryRawVelocity, spatialIndex4, PiLp.toLp_apply, PiLp.sub_apply]
      using congrArg (fun v : Vec => v i) hraw
  have hκ := reconstruction_lorentzTrace_boundary K t x
  have hB : lowerTensor4
      (conservedSourceUpper ν ρ (boundaryVelocity K) (boundaryPressure ρ K) t x +
        scalarCompletionUpper (boundaryPotential K) t x) = traceRecover4 (K t x) := by
    ext a b
    change lowerTensor4
      (conservedSourceUpper ν ρ (boundaryVelocity K) (boundaryPressure ρ K) t x +
        scalarCompletionUpper (boundaryPotential K) t x) a b =
      lorentzTrace4 (K t x) * eta4 a b - K t x a b
    rw [hκ]
    refine Fin.cases ?_ (fun i => ?_) a
    · refine Fin.cases ?_ (fun j => ?_) b
      · rw [lowerTensor4_time_time]
        change ρ + scalarLaplacian (boundaryPotential K t) x =
          (-K t x 0 0 - boundaryBeta K t x) * (-1) - K t x 0 0
        rw [hΔ]
        ring
      · rw [lowerTensor4_time_space]
        have hη : eta4 0 j.succ = 0 := by simp [eta4]
        rw [hη]
        change -(boundaryVelocity K t x j +
          -gradient (scalarLocalTimeDerivative (boundaryPotential K) t) x j) =
          (-K t x 0 0 - boundaryBeta K t x) * 0 - K t x 0 j.succ
        rw [hw j]
        ring
    · refine Fin.cases ?_ (fun j => ?_) b
      · have hlower (T : Tensor4) : lowerTensor4 T i.succ 0 = -T i.succ 0 := by
          simp [lowerTensor4, lorentzSign4]
        rw [hlower]
        have hη : eta4 i.succ 0 = 0 := by simp [eta4]
        rw [hη]
        change -(boundaryVelocity K t x i +
          -gradient (scalarLocalTimeDerivative (boundaryPotential K) t) x i) =
          (-K t x 0 0 - boundaryBeta K t x) * 0 - K t x i.succ 0
        rw [hsym.apply 0 i.succ, hw i]
        ring
      · rw [lowerTensor4_space_space, reconstruction_eta4_spatial]
        change boundaryVelocity K t x i * boundaryVelocity K t x j +
          boundaryPressure ρ K t x * identity3 i j -
          ν * strain (boundaryVelocity K t) x i j +
          (scalarHessian (boundaryPotential K t) x i j +
            (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t x -
              scalarLaplacian (boundaryPotential K t) x) * identity3 i j) =
          (-K t x 0 0 - boundaryBeta K t x) * identity3 i j - K t x i.succ j.succ
        rw [boundarySpatial_eq_of_stress_zero ν ρ K t x hdiv hΔ hF i j, hΔ]
        simp only [boundaryPressure]
        ring
  symm
  unfold completedBoundary
  rw [hB, traceReverse4_traceRecover4]

/-- Full spatial slices, matching the germ interface used by the adapter. -/
theorem boundary_slice_eq_completedBoundary_of_zero_stress
    (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ)
    (hsym : ∀ x, (K t x).IsSymm)
    (hdiv : ∀ x, divergence (boundaryVelocity K t) x = 0)
    (hΔ : ∀ x, scalarLaplacian (boundaryPotential K t) x = boundaryBeta K t x - ρ)
    (hraw : ∀ x, boundaryRawVelocity K t x = boundaryVelocity K t x -
      gradient (scalarLocalTimeDerivative (boundaryPotential K) t) x)
    (hF : ∀ x, boundaryStress ν K t x = 0) :
    K t = completedBoundary ν ρ (boundaryVelocity K)
      (boundaryPressure ρ K) (boundaryPotential K) t := by
  funext x
  exact boundary_eq_completedBoundary_of_zero_stress ν ρ K t x
    (hsym x) (hdiv x) (hΔ x) (hraw x) (hF x)

/-- Exact residual assembly from four lower differential identities. These
hypotheses still require the native analytic/geometry proofs; this theorem
only carries out their nontrivial cancellation in the actual PDE operators. -/
theorem reconstruction_residual_of_differential_identities
    (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hCodazzi : localTimeDerivative (boundaryRawVelocity K) t x =
      tensorDivergence (boundarySpatialTensor K t) x +
        gradient (fun y => K t y 0 0) x + gradient (boundaryBeta K t) x)
    (hHodgeTime : localTimeDerivative (boundaryVelocity K) t x =
      localTimeDerivative (boundaryRawVelocity K) t x +
        gradient (scalarLocalTimeDerivative
          (scalarLocalTimeDerivative (boundaryPotential K)) t) x)
    (hPressure : gradient (boundaryPressure ρ K t) x =
      -gradient (fun y => K t y 0 0) x -
        (1 / 3 : ℝ) • gradient
          (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x -
        gradient (scalarLocalTimeDerivative
          (scalarLocalTimeDerivative (boundaryPotential K)) t) x)
    (hStress : tensorDivergence (boundaryStress ν K t) x =
      tensorDivergence (boundarySpatialTensor K t) x + convection (boundaryVelocity K t) x +
        gradient (boundaryBeta K t) x - ν • laplacian (boundaryVelocity K t) x -
        (1 / 3 : ℝ) • gradient
          (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x) :
    nseResidual ν (boundaryVelocity K) (boundaryPressure ρ K) t x =
      tensorDivergence (boundaryStress ν K t) x := by
  unfold nseResidual
  rw [hHodgeTime, hCodazzi, hPressure, hStress]
  abel

end
end NSEGR
