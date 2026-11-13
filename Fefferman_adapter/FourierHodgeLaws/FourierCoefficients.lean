import FourierHodgeLaws.TargetPrimitives
import SingularClosure.SmoothDatumSobolev
import SingularClosure.SobolevSmoothRealization

/-!
Rapid Fourier coefficients of the actual smooth periodic target fields.
All Sobolev memberships are proved from the original smoothness hypothesis.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical

noncomputable section

theorem scalarLift_coordinateDerivative (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    coordinateDerivative (scalarLift f) j =
      scalarLift (fun x => fderiv ℝ f x (unitVector j)) := by
  funext x
  ext i
  have hd := ((scalarLift_contDiff f hf).differentiable (by simp) x).hasFDerivAt
  have hp := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x hd
  have hr := (hf.differentiable (by simp) x).hasFDerivAt
  have he := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector j)) (hp.unique hr)
  simpa only [coordinateDerivative, ContinuousLinearMap.comp_apply,
    EuclideanSpace.coe_proj, scalarLift_component] using he

theorem datumFourierCoeff_coordinateDerivative (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (j : Fin 3) :
    SingularClosure.datumFourierCoeff (coordinateDerivative a j) =
      SingularClosure.spectralMultiplier (SingularClosure.derivativeSymbol j)
        (SingularClosure.datumFourierCoeff a) := by
  exact SingularClosure.datumFourierCoeff_coordinateDerivative j a ha hp

theorem scalarCoeff_coordinateDerivative (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) (k : Frequency) :
    scalarCoeff (fun x => fderiv ℝ f x (unitVector j)) k =
      SingularClosure.derivativeSymbol j k * scalarCoeff f k := by
  have h := congrFun (congrFun (datumFourierCoeff_coordinateDerivative (scalarLift f)
    (scalarLift_contDiff f hf) (scalarLift_periodic f hp) j) k) (0 : Fin 3)
  rw [scalarLift_coordinateDerivative f hf j] at h
  exact h

theorem rapid_datumFourierCoeff (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    SingularClosure.RapidScalarFourier (fun k => SingularClosure.datumFourierCoeff a k i) := by
  exact SingularClosure.ALL_SOBOLEV_IMP_RAPID_SCALAR
    (SingularClosure.datumFourierCoeff a)
    (fun s => SingularClosure.SMOOTH_DATUM_MEM_TORUS_SOBOLEV s a ha hp) i

theorem rapid_scalarCoeff (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    SingularClosure.RapidScalarFourier (scalarCoeff f) := by
  exact rapid_datumFourierCoeff (scalarLift f)
    (scalarLift_contDiff f hf) (scalarLift_periodic f hp) 0

theorem rapid_mul_bounded {b w : Frequency → ℂ}
    (hb : SingularClosure.RapidScalarFourier b)
    (hw : ∀ k, ‖w k‖ ≤ 1) :
    SingularClosure.RapidScalarFourier (fun k => w k * b k) := by
  intro m
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) _ (hb m)
  intro k
  calc
    _ = (‖w k‖ * ‖b k‖) * ‖SingularClosure.fourierPhaseCLM k‖ ^ m := by
      rw [norm_mul]
    _ ≤ (1 * ‖b k‖) * ‖SingularClosure.fourierPhaseCLM k‖ ^ m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _))
        (pow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [one_mul]

theorem rapid_inverseLaplacianCoeff (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    SingularClosure.RapidScalarFourier (fun k => inverseVectorCoeff a k i) := by
  exact rapid_mul_bounded (rapid_datumFourierCoeff a ha hp i)
    inverseLaplacianSymbol_complex_norm_le_one

theorem rapid_inverseScalarCoeff (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    SingularClosure.RapidScalarFourier (inverseScalarCoeff f) := by
  exact rapid_mul_bounded (rapid_scalarCoeff f hf hp)
    inverseLaplacianSymbol_complex_norm_le_one

theorem inverseVectorCoeff_weighted_summable (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) (m : ℕ) :
    Summable (fun k => ‖inverseVectorCoeff a k i‖ *
      ‖SingularClosure.fourierPhaseCLM k‖ ^ m) :=
  rapid_inverseLaplacianCoeff a ha hp i m

theorem inverseScalarCoeff_weighted_summable (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (m : ℕ) :
    Summable (fun k => ‖inverseScalarCoeff f k‖ *
      ‖SingularClosure.fourierPhaseCLM k‖ ^ m) :=
  rapid_inverseScalarCoeff f hf hp m

end

end NSEMaxwell.HodgeProof
