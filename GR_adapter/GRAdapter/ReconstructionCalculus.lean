import GRAdapter.ReconstructionAlgebra

/-!
# Native pressure calculus in the reconstruction identity

The pressure derivative follows from the actual pressure definition and
pointwise differentiability of its three nonconstant summands. The
Codazzi, differentiated Hodge and stress-divergence identities remain
explicit lower-level hypotheses in the residual theorem.
-/

set_option autoImplicit false

namespace NSEGR
noncomputable section

/-- The actual decoded pressure has the derivative dictated by its formula.
Only spatial differentiability at the point is required. -/
theorem boundaryPressure_hasFDerivAt (ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hk : DifferentiableAt ℝ (fun y => K t y 0 0) x)
    (huSq : DifferentiableAt ℝ
      (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x)
    (hq : DifferentiableAt ℝ
      (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x) :
    HasFDerivAt (boundaryPressure ρ K t)
      (-fderiv ℝ (fun y => K t y 0 0) x -
        (1 / 3 : ℝ) • fderiv ℝ
          (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x -
        fderiv ℝ
          (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x) x := by
  have hp : boundaryPressure ρ K t = fun y =>
      -K t y 0 0 - (1 / 3 : ℝ) •
        (2 * ρ + vectorSq3 (fun i => boundaryVelocity K t y i)) -
        scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t y := by
    funext y
    dsimp [boundaryPressure]
    simp only [smul_eq_mul]
    ring
  rw [hp]
  exact (hk.hasFDerivAt.neg.sub
    ((huSq.hasFDerivAt.const_add (2 * ρ)).const_smul (1 / 3 : ℝ))).sub hq.hasFDerivAt

/-- The pressure-gradient premise in the residual identity is discharged
by the three pointwise differentiability hypotheses. -/
theorem boundaryPressure_gradient (ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hk : DifferentiableAt ℝ (fun y => K t y 0 0) x)
    (huSq : DifferentiableAt ℝ
      (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x)
    (hq : DifferentiableAt ℝ
      (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x) :
    gradient (boundaryPressure ρ K t) x =
      -gradient (fun y => K t y 0 0) x -
        (1 / 3 : ℝ) • gradient
          (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x -
        gradient (scalarLocalTimeDerivative
          (scalarLocalTimeDerivative (boundaryPotential K)) t) x := by
  apply PiLp.ext
  intro i
  change fderiv ℝ (boundaryPressure ρ K t) x (unitVector i) =
    -(fderiv ℝ (fun y => K t y 0 0) x (unitVector i)) -
      (1 / 3 : ℝ) •
        (fderiv ℝ (fun y => vectorSq3 (fun j => boundaryVelocity K t y j)) x
          (unitVector i)) -
      fderiv ℝ
        (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x
        (unitVector i)
  rw [(boundaryPressure_hasFDerivAt ρ K t x hk huSq hq).fderiv]
  rfl

/-- Exact native residual identity with the pressure derivative proved.
The remaining differential identities concern geometry, Hodge commutation,
and the divergence of the actual constitutive tensor. -/
theorem reconstruction_residual_of_three_differential_identities
    (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hk : DifferentiableAt ℝ (fun y => K t y 0 0) x)
    (huSq : DifferentiableAt ℝ
      (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x)
    (hq : DifferentiableAt ℝ
      (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x)
    (hCodazzi : localTimeDerivative (boundaryRawVelocity K) t x =
      tensorDivergence (boundarySpatialTensor K t) x +
        gradient (fun y => K t y 0 0) x + gradient (boundaryBeta K t) x)
    (hHodgeTime : localTimeDerivative (boundaryVelocity K) t x =
      localTimeDerivative (boundaryRawVelocity K) t x +
        gradient (scalarLocalTimeDerivative
          (scalarLocalTimeDerivative (boundaryPotential K)) t) x)
    (hStress : tensorDivergence (boundaryStress ν K t) x =
      tensorDivergence (boundarySpatialTensor K t) x + convection (boundaryVelocity K t) x +
        gradient (boundaryBeta K t) x - ν • laplacian (boundaryVelocity K t) x -
        (1 / 3 : ℝ) • gradient
          (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x) :
    nseResidual ν (boundaryVelocity K) (boundaryPressure ρ K) t x =
      tensorDivergence (boundaryStress ν K t) x := by
  exact reconstruction_residual_of_differential_identities ν ρ K t x
    hCodazzi hHodgeTime (boundaryPressure_gradient ρ K t x hk huSq hq) hStress

end
end NSEGR
