import GRAdapter.ReconstructionCalculus
import GRAdapter.UnitTorus

/-! Native differential identities for the constitutive tensor. The proofs
use the actual Fréchet derivatives and smoothness; mixed-derivative and
stress-divergence equations are not assumed. -/

set_option autoImplicit false

namespace NSEGR
open scoped BigOperators ContDiff
noncomputable section

namespace StressCalc

def secondSpatial (a : Field) (i j : Fin 3) (x : Vec) : Vec :=
  fderiv ℝ (fderiv ℝ a) x (unitVector i) (unitVector j)

theorem component_fderiv {a : Field} {x : Vec}
    (ha : DifferentiableAt ℝ a x) (v : Vec) (i : Fin 3) :
    fderiv ℝ (fun y => a y i) x v = (fderiv ℝ a x v) i := by
  have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (a x) i).comp x ha.hasFDerivAt
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L v) h.fderiv

theorem partial_component_smooth {a : Field} (ha : ContDiff ℝ ∞ a) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialPartial a i x j) :=
  (contDiff_piLp 2).mp (spatialPartial_smooth ha i) j

theorem partial_partial {a : Field} (ha : ContDiff ℝ ∞ a)
    (i j : Fin 3) (x : Vec) :
    spatialPartial (spatialPartial a j) i x = secondSpatial a i j x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have h := (hd.differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (unitVector j) x)
  have he := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i)) h.fderiv
  change fderiv ℝ (fun y => fderiv ℝ a y (unitVector j)) x (unitVector i) =
    fderiv ℝ (fderiv ℝ a) x (unitVector i) (unitVector j)
  simpa [ContinuousLinearMap.flip_apply] using he

theorem secondSpatial_symm {a : Field} (ha : ContDiff ℝ ∞ a)
    (i j : Fin 3) (x : Vec) :
    secondSpatial a i j x = secondSpatial a j i x := by
  exact (ha.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    decide)) (unitVector i) (unitVector j)

theorem partial_component_fderiv {a : Field} (ha : ContDiff ℝ ∞ a)
    (i j k : Fin 3) (x : Vec) :
    fderiv ℝ (fun y => spatialPartial a j y k) x (unitVector i) =
      secondSpatial a i j x k := by
  calc
    _ = spatialPartial (spatialPartial a j) i x k :=
      component_fderiv ((spatialPartial_smooth ha j).differentiable (by simp) x)
        (unitVector i) k
    _ = _ := congrArg (fun v : Vec => v k) (partial_partial ha i j x)

theorem gradient_divergence_component {a : Field} (ha : ContDiff ℝ ∞ a)
    (i : Fin 3) (x : Vec) :
    gradient (divergence a) x i =
      ∑ j : Fin 3, secondSpatial a i j x j := by
  change fderiv ℝ (fun y => ∑ j : Fin 3, spatialPartial a j y j) x (unitVector i) = _
  rw [fderiv_fun_sum (fun j _ =>
    (partial_component_smooth ha j j).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sum_apply, partial_component_fderiv ha]

theorem laplacian_component {a : Field} (ha : ContDiff ℝ ∞ a)
    (x : Vec) (i : Fin 3) :
    laplacian a x i = ∑ j : Fin 3, secondSpatial a j j x i := by
  have hsec (j : Fin 3) : fderiv ℝ (spatialPartial a j) x (unitVector j) =
      secondSpatial a j j x := partial_partial ha j j x
  simp [laplacian, hsec, Fin.sum_univ_succ, add_assoc]

theorem vector_decomposition (v : Vec) :
    v = v 0 • unitVector 0 + v 1 • unitVector 1 + v 2 • unitVector 2 := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [unitVector, EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]

theorem convection_component (a : Field) (x : Vec) (i : Fin 3) :
    convection a x i = a x 0 * spatialPartial a 0 x i +
      a x 1 * spatialPartial a 1 x i + a x 2 * spatialPartial a 2 x i := by
  have h := congrArg (fun v : Vec => fderiv ℝ a x v) (vector_decomposition (a x))
  have hi := congrArg (fun v : Vec => v i) h
  simpa only [convection, spatialPartial, map_add, map_smul,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hi

end StressCalc

/-- The compressible identity is proved before imposing solenoidality. -/
theorem tensorDivergence_strain {a : Field} (ha : ContDiff ℝ ∞ a) (x : Vec) :
    tensorDivergence (strain a) x = gradient (divergence a) x + laplacian a x := by
  have hd (i j : Fin 3) :
      fderiv ℝ (fun y => strain a y i j) x (unitVector j) =
        StressCalc.secondSpatial a j i x j + StressCalc.secondSpatial a j j x i := by
    change fderiv ℝ
      (fun y => spatialPartial a i y j + spatialPartial a j y i) x (unitVector j) = _
    rw [fderiv_fun_add
      ((StressCalc.partial_component_smooth ha i j).differentiable (by simp) x)
      ((StressCalc.partial_component_smooth ha j i).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, StressCalc.partial_component_fderiv ha]
  apply PiLp.ext
  intro i
  simp only [tensorDivergence, PiLp.toLp_apply, PiLp.add_apply, hd,
    Finset.sum_add_distrib, StressCalc.gradient_divergence_component ha,
    StressCalc.laplacian_component ha]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : Vec => v j) (StressCalc.secondSpatial_symm ha j i x)

theorem tensorDivergence_strain_of_divergence_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hdiv : divergence a = 0) (x : Vec) :
    tensorDivergence (strain a) x = laplacian a x := by
  rw [tensorDivergence_strain ha x, hdiv, gradient_zero]
  simp

/-- Actual STF strain has the viscous divergence for solenoidal fields. -/
theorem tensorDivergence_tf3_strain_of_divergence_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hdiv : divergence a = 0) (x : Vec) :
    tensorDivergence (fun y => tf3 (strain a y)) x = laplacian a x := by
  have heq : (fun y => tf3 (strain a y)) = strain a := by
    funext y
    apply tf3_eq_self_of_trace_zero
    rw [trace3_eq_matrix_trace, trace_strain, hdiv]
    simp
  rw [heq]
  exact tensorDivergence_strain_of_divergence_zero ha hdiv x

/-- The full product-rule identity retains the compressible correction. -/
theorem tensorDivergence_velocityOuter {a : Field} {x : Vec}
    (ha : DifferentiableAt ℝ a x) :
    tensorDivergence (fun y => velocityOuter (a y)) x =
      convection a x + divergence a x • a x := by
  have hc (i : Fin 3) : DifferentiableAt ℝ (fun y => a y i) x :=
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (a x) i).comp x ha.hasFDerivAt).differentiableAt
  have hd (i j : Fin 3) :
      fderiv ℝ (fun y => velocityOuter (a y) i j) x (unitVector j) =
        a x i * spatialPartial a j x j + a x j * spatialPartial a j x i := by
    change fderiv ℝ (fun y => a y i * a y j) x (unitVector j) = _
    rw [fderiv_fun_mul (hc i) (hc j)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, StressCalc.component_fderiv ha, spatialPartial]
  apply PiLp.ext
  intro i
  simp [tensorDivergence, hd, Fin.sum_univ_succ, divergence,
    StressCalc.convection_component, smul_eq_mul]
  ring

theorem tensorDivergence_velocityOuter_of_divergence_zero {a : Field} {x : Vec}
    (ha : DifferentiableAt ℝ a x) (hdiv : divergence a x = 0) :
    tensorDivergence (fun y => velocityOuter (a y)) x = convection a x := by
  rw [tensorDivergence_velocityOuter ha, hdiv, zero_smul, add_zero]

theorem divergence_gradient {f : ScalarField} (hf : ContDiff ℝ ∞ f) :
    divergence (gradient f) = scalarLaplacian f := by
  funext x
  unfold divergence scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  exact (StressCalc.component_fderiv
    ((gradient_smooth hf).differentiable (by simp) x) (unitVector i) i).symm

/-- The third-order identity follows from smooth mixed-derivative symmetry. -/
theorem tensorDivergence_scalarHessian {f : ScalarField} (hf : ContDiff ℝ ∞ f)
    (x : Vec) :
    tensorDivergence (scalarHessian f) x = gradient (scalarLaplacian f) x := by
  have hg := gradient_smooth hf
  have hH (i j : Fin 3) :
      (fun y => scalarHessian f y i j) = (fun y => spatialPartial (gradient f) i y j) := by
    funext y
    exact StressCalc.component_fderiv (hg.differentiable (by simp) y) (unitVector i) j
  rw [← divergence_gradient hf]
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3, fderiv ℝ (fun y => scalarHessian f y i j) x (unitVector j)) = _
  simp only [hH, StressCalc.partial_component_fderiv hg,
    StressCalc.gradient_divergence_component hg]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : Vec => v j) (StressCalc.secondSpatial_symm hg j i x)

theorem tensorDivergence_add (A B : TensorField) (x : Vec)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x) :
    tensorDivergence (fun y => A y + B y) x =
      tensorDivergence A x + tensorDivergence B x := by
  have hd (i j : Fin 3) := fderiv_fun_add (hA i j) (hB i j)
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3, fderiv ℝ (fun y => A y i j + B y i j) x (unitVector j)) =
    (∑ j : Fin 3, fderiv ℝ (fun y => A y i j) x (unitVector j)) +
      ∑ j : Fin 3, fderiv ℝ (fun y => B y i j) x (unitVector j)
  simp only [hd, ContinuousLinearMap.add_apply, Finset.sum_add_distrib]

theorem tensorDivergence_sub (A B : TensorField) (x : Vec)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x) :
    tensorDivergence (fun y => A y - B y) x =
      tensorDivergence A x - tensorDivergence B x := by
  have hd (i j : Fin 3) := fderiv_fun_sub (hA i j) (hB i j)
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3, fderiv ℝ (fun y => A y i j - B y i j) x (unitVector j)) =
    (∑ j : Fin 3, fderiv ℝ (fun y => A y i j) x (unitVector j)) -
      ∑ j : Fin 3, fderiv ℝ (fun y => B y i j) x (unitVector j)
  simp only [hd, ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib]

theorem tensorDivergence_smul (c : ℝ) (A : TensorField) (x : Vec)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    tensorDivergence (fun y => c • A y) x = c • tensorDivergence A x := by
  have hd (i j : Fin 3) := fderiv_fun_const_smul (hA i j) c
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3, fderiv ℝ (fun y => c • A y i j) x (unitVector j)) =
    c • ∑ j : Fin 3, fderiv ℝ (fun y => A y i j) x (unitVector j)
  simp only [hd, ContinuousLinearMap.smul_apply, Finset.smul_sum]

theorem tensorDivergence_isotropic (f : ScalarField) (x : Vec)
    (hf : DifferentiableAt ℝ f x) :
    tensorDivergence (fun y i j => f y * identity3 i j) x = gradient f x := by
  have hd (i j : Fin 3) :
      fderiv ℝ (fun y => f y * identity3 i j) x = identity3 i j • fderiv ℝ f x := by
    simpa only [mul_comm] using fderiv_const_mul hf (identity3 i j)
  apply PiLp.ext
  intro i
  change (∑ j : Fin 3, fderiv ℝ (fun y => f y * identity3 i j) x (unitVector j)) =
    fderiv ℝ f x (unitVector i)
  simp only [hd, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp [identity3]

theorem scalarHessian_component_smooth {f : ScalarField} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => scalarHessian f x i j) := by
  have hg := gradient_smooth hf
  have heq : (fun x => scalarHessian f x i j) =
      (fun x => spatialPartial (gradient f) i x j) := by
    funext x
    exact StressCalc.component_fderiv (hg.differentiable (by simp) x) (unitVector i) j
  rw [heq]
  exact StressCalc.partial_component_smooth hg i j

theorem strain_component_smooth {a : Field} (ha : ContDiff ℝ ∞ a)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => strain a x i j) :=
  (StressCalc.partial_component_smooth ha i j).add
    (StressCalc.partial_component_smooth ha j i)

theorem velocityOuter_component_smooth {a : Field} (ha : ContDiff ℝ ∞ a)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => velocityOuter (a x) i j) :=
  ((contDiff_piLp 2).mp ha i).mul ((contDiff_piLp 2).mp ha j)

theorem vectorSq3_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun x => vectorSq3 (fun i => a x i)) :=
  ((((contDiff_piLp 2).mp ha 0).pow 2).add
    (((contDiff_piLp 2).mp ha 1).pow 2)).add (((contDiff_piLp 2).mp ha 2).pow 2)

/-- The actual constitutive stress divergence, derived from smoothness,
solenoidality and the scalar Poisson equation. No stress-divergence premise
or mixed-derivative identity is supplied. -/
theorem boundaryStress_tensorDivergence
    (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => boundarySpatialTensor K t y i j) x)
    (hu : ContDiff ℝ ∞ (boundaryVelocity K t))
    (hq : ContDiff ℝ ∞ (boundaryPotential K t))
    (hdiv : divergence (boundaryVelocity K t) = 0)
    (hΔ : ∀ y, scalarLaplacian (boundaryPotential K t) y = boundaryBeta K t y - ρ) :
    tensorDivergence (boundaryStress ν K t) x =
      tensorDivergence (boundarySpatialTensor K t) x + convection (boundaryVelocity K t) x +
        gradient (boundaryBeta K t) x - ν • laplacian (boundaryVelocity K t) x -
        (1 / 3 : ℝ) • gradient
          (fun y => vectorSq3 (fun i => boundaryVelocity K t y i)) x := by
  let A := boundarySpatialTensor K t
  let u := boundaryVelocity K t
  let q := boundaryPotential K t
  let O : TensorField := fun y => velocityOuter (u y)
  let H : TensorField := scalarHessian q
  let Z : TensorField := strain u
  let T : TensorField := fun y => A y + O y + H y - ν • Z y
  let s : ScalarField := fun y => vectorSq3 (fun i => u y i)
  let r : ScalarField := fun y => (s y - ρ) / 3
  let I : TensorField := fun y i j => r y * identity3 i j
  have ho (i j : Fin 3) : DifferentiableAt ℝ (fun y => O y i j) x :=
    (velocityOuter_component_smooth hu i j).differentiable (by simp) x
  have hh (i j : Fin 3) : DifferentiableAt ℝ (fun y => H y i j) x :=
    (scalarHessian_component_smooth hq i j).differentiable (by simp) x
  have hz (i j : Fin 3) : DifferentiableAt ℝ (fun y => Z y i j) x :=
    (strain_component_smooth hu i j).differentiable (by simp) x
  have hs : DifferentiableAt ℝ s x := (vectorSq3_smooth hu).differentiable (by simp) x
  have hr : HasFDerivAt r ((1 / 3 : ℝ) • fderiv ℝ s x) x := by
    have heq : r = fun y => (1 / 3 : ℝ) • (s y - ρ) := by
      funext y
      dsimp [r]
      ring
    rw [heq]
    exact (hs.hasFDerivAt.sub_const ρ).const_smul (1 / 3 : ℝ)
  have hgrad : gradient r x = (1 / 3 : ℝ) • gradient s x := by
    apply PiLp.ext
    intro i
    change fderiv ℝ r x (unitVector i) = (1 / 3 : ℝ) • fderiv ℝ s x (unitVector i)
    rw [hr.fderiv]
    rfl
  have ht (i j : Fin 3) : DifferentiableAt ℝ (fun y => T y i j) x :=
    (((hA i j).add (ho i j)).add (hh i j)).sub ((hz i j).const_smul ν)
  have hi (i j : Fin 3) : DifferentiableAt ℝ (fun y => I y i j) x :=
    hr.differentiableAt.mul_const (identity3 i j)
  have htrace (y : Vec) : trace3 (T y) = s y - ρ :=
    boundaryPreStress_trace ν ρ K t y (congrFun hdiv y) (hΔ y)
  have hF : boundaryStress ν K t = fun y => T y - I y := by
    funext y
    ext i j
    change T y i j - (trace3 (T y) / 3) * identity3 i j = T y i j - r y * identity3 i j
    simp only [htrace, r]
  have hDT : tensorDivergence T x =
      tensorDivergence A x + tensorDivergence O x + tensorDivergence H x -
        ν • tensorDivergence Z x := by
    have hAO (i j : Fin 3) : DifferentiableAt ℝ (fun y => (A y + O y) i j) x :=
      (hA i j).add (ho i j)
    have hAOH (i j : Fin 3) : DifferentiableAt ℝ (fun y => (A y + O y + H y) i j) x :=
      (hAO i j).add (hh i j)
    have hνZ (i j : Fin 3) : DifferentiableAt ℝ (fun y => (ν • Z y) i j) x :=
      (hz i j).const_smul ν
    change tensorDivergence (fun y => (A y + O y + H y) - ν • Z y) x = _
    rw [tensorDivergence_sub (fun y => A y + O y + H y) (fun y => ν • Z y) x hAOH hνZ]
    rw [tensorDivergence_add (fun y => A y + O y) H x hAO hh,
      tensorDivergence_add A O x hA ho, tensorDivergence_smul ν Z x hz]
  have hLap : scalarLaplacian q = fun y => boundaryBeta K t y - ρ := funext hΔ
  have hGradLap : gradient (scalarLaplacian q) x = gradient (boundaryBeta K t) x := by
    rw [hLap]
    apply PiLp.ext
    intro i
    change fderiv ℝ (fun y => boundaryBeta K t y - ρ) x (unitVector i) =
      fderiv ℝ (boundaryBeta K t) x (unitVector i)
    rw [fderiv_sub_const]
  rw [hF, tensorDivergence_sub T I x ht hi]
  change tensorDivergence T x - tensorDivergence (fun y i j => r y * identity3 i j) x = _
  rw [hDT, tensorDivergence_isotropic r x hr.differentiableAt, hgrad]
  rw [tensorDivergence_velocityOuter_of_divergence_zero
      (hu.differentiable (by simp) x) (congrFun hdiv x),
    tensorDivergence_scalarHessian hq x, hGradLap,
    tensorDivergence_strain_of_divergence_zero hu hdiv x]

/-- Pressure and stress differentiation are now proved; the remaining
equational inputs are Codazzi evolution and differentiated Hodge inversion. -/
theorem reconstruction_residual_of_codazzi_hodge
    (ν ρ : ℝ) (K : BoundaryTensor) (t : ℝ) (x : Vec)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => boundarySpatialTensor K t y i j) x)
    (hu : ContDiff ℝ ∞ (boundaryVelocity K t))
    (hq : ContDiff ℝ ∞ (boundaryPotential K t))
    (hdiv : divergence (boundaryVelocity K t) = 0)
    (hΔ : ∀ y, scalarLaplacian (boundaryPotential K t) y = boundaryBeta K t y - ρ)
    (hk : DifferentiableAt ℝ (fun y => K t y 0 0) x)
    (hqtt : DifferentiableAt ℝ
      (scalarLocalTimeDerivative (scalarLocalTimeDerivative (boundaryPotential K)) t) x)
    (hCodazzi : localTimeDerivative (boundaryRawVelocity K) t x =
      tensorDivergence (boundarySpatialTensor K t) x +
        gradient (fun y => K t y 0 0) x + gradient (boundaryBeta K t) x)
    (hHodgeTime : localTimeDerivative (boundaryVelocity K) t x =
      localTimeDerivative (boundaryRawVelocity K) t x +
        gradient (scalarLocalTimeDerivative
          (scalarLocalTimeDerivative (boundaryPotential K)) t) x) :
    nseResidual ν (boundaryVelocity K) (boundaryPressure ρ K) t x =
      tensorDivergence (boundaryStress ν K t) x := by
  exact reconstruction_residual_of_three_differential_identities ν ρ K t x hk
    ((vectorSq3_smooth hu).differentiable (by simp) x) hqtt hCodazzi hHodgeTime
    (boundaryStress_tensorDivergence ν ρ K t x hA hu hq hdiv hΔ)

end
end NSEGR
