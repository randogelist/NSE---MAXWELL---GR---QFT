import GRAssembly.Strengthening.PressureIdentification
import GRAssembly.Strengthening.PhysicalFourierNSE
import SingularClosure.InfiniteFourierPressure

/-!
Identification of the literal native quadratic Poisson pressure with the
literal full Fourier transport pressure. All coefficients are cube integrals;
all summability is derived from actual smooth periodic spatial fields.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff BigOperators

namespace NSEGR.Strengthening
noncomputable section

def normalizedFullTransportPressure (c : SingularClosure.TorusSobolev 0) : ScalarField :=
  fun x => SingularClosure.fullTransportPressure c x - SingularClosure.fullTransportPressure c 0

theorem physical_pressure_gradient_coeff
    (ν : ℝ) (v d : Field) (p : ScalarField)
    (hv : ContDiff ℝ ∞ v) (hvper : SpatialPeriodic v)
    (hdivv : ∀ x, divergence v x = 0)
    (hd : ContDiff ℝ ∞ d) (hdper : SpatialPeriodic d)
    (hdivd : ∀ x, divergence d x = 0)
    (hp : ContDiff ℝ ∞ p) (hpper : SpatialPeriodic p)
    (hmom : ∀ x, d x + convection v x + gradient p x = ν • laplacian v x) :
    SingularClosure.datumFourierCoeff (gradient p) = fun k i =>
      SingularClosure.coefficientLeray k
        (SingularClosure.fullTransportCoefficients (physicalFourierValue 0 v) k) i -
      SingularClosure.fullTransportCoefficients (physicalFourierValue 0 v) k i := by
  have hconv : Continuous (convection v) :=
    (NSEMaxwell.PeriodicIntegration.convection_smooth hv).continuous
  have hgrad : Continuous (gradient p) := (gradient_smooth hp).continuous
  have hlapcoeff : SingularClosure.datumFourierCoeff (laplacian v) =
      SingularClosure.laplacianCoefficient (SingularClosure.datumFourierCoeff v) :=
    NSEMaxwell.HodgeProof.datumFourierCoeff_laplacian v hv hvper
  have hconvcoeff : SingularClosure.datumFourierCoeff (convection v) =
      SingularClosure.fullTransportCoefficients (physicalFourierValue 0 v) :=
    physicalFourierValue_convection_coeff v hv hvper hdivv
  have hprojectedGradient : SingularClosure.fourierLerayLinear
      (SingularClosure.datumFourierCoeff (gradient p)) = 0 :=
    fourierLeray_gradient_zero p hp hpper
  have he : d + convection v + gradient p = ν • laplacian v := funext hmom
  have hf := congrArg SingularClosure.datumFourierCoeff he
  rw [NSEMaxwell.HodgeProof.datumFourierCoeff_add (d + convection v) (gradient p)
      (hd.continuous.add hconv) hgrad,
    NSEMaxwell.HodgeProof.datumFourierCoeff_add d (convection v) hd.continuous hconv,
    datumFourierCoeff_real_smul, hlapcoeff, hconvcoeff] at hf
  have hprojected := congrArg SingularClosure.fourierLerayLinear hf
  rw [map_add, map_add, map_smul,
    hprojectedGradient,
    fourierLeray_eq_of_solenoidal (SingularClosure.datumFourierCoeff d)
      (datumFourierCoeff_solenoidal_of_divergence_free d hd hdper hdivd),
    fourierLeray_eq_of_solenoidal
      (SingularClosure.laplacianCoefficient (SingularClosure.datumFourierCoeff v))
      (laplacianCoefficient_solenoidal _
        (datumFourierCoeff_solenoidal_of_divergence_free v hv hvper hdivv)),
    add_zero] at hprojected
  funext k i
  have hki := congrFun (congrFun hf k) i
  have hpki := congrFun (congrFun hprojected k) i
  change SingularClosure.datumFourierCoeff d k i +
      SingularClosure.fullTransportCoefficients (physicalFourierValue 0 v) k i +
      SingularClosure.datumFourierCoeff (gradient p) k i =
    (ν : ℂ) * SingularClosure.laplacianCoefficient
      (SingularClosure.datumFourierCoeff v) k i at hki
  change SingularClosure.datumFourierCoeff d k i +
      SingularClosure.coefficientLeray k
        (SingularClosure.fullTransportCoefficients (physicalFourierValue 0 v) k) i =
    (ν : ℂ) * SingularClosure.laplacianCoefficient
      (SingularClosure.datumFourierCoeff v) k i at hpki
  linear_combination hki - hpki

theorem normalized_pressure_eq_fullTransportPressure
    (ν : ℝ) (v d : Field) (p : ScalarField)
    (hv : ContDiff ℝ ∞ v) (hvper : SpatialPeriodic v)
    (hdivv : ∀ x, divergence v x = 0)
    (hd : ContDiff ℝ ∞ d) (hdper : SpatialPeriodic d)
    (hdivd : ∀ x, divergence d x = 0)
    (hp : ContDiff ℝ ∞ p) (hpper : SpatialPeriodic p)
    (hmom : ∀ x, d x + convection v x + gradient p x = ν • laplacian v x) :
    (fun x => p x - p 0) = normalizedFullTransportPressure (physicalFourierValue 0 v) := by
  let c := physicalFourierValue 0 v
  have hcoeff : c.val = SingularClosure.datumFourierCoeff v :=
    physicalFourierValue_coeff 0 v hv hvper
  have hall : ∀ s : ℕ, Memℓp (SingularClosure.sobolevWeightedCoeff s c.val) 2 := by
    intro s
    rw [hcoeff]
    exact SingularClosure.SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv hvper
  have hreal : SingularClosure.SpectralReality c.val := by
    rw [hcoeff]
    exact SingularClosure.datumFourierCoeff_reality v
  have hsol : SingularClosure.SpectralSolenoidal c.val := by
    rw [hcoeff]
    exact datumFourierCoeff_solenoidal_of_divergence_free v hv hvper hdivv
  have hq : ContDiff ℝ ∞ (SingularClosure.fullTransportPressure c) :=
    SingularClosure.fullTransportPressure_contDiff c hall hreal hsol
  have hqper : SpatialPeriodic (SingularClosure.fullTransportPressure c) :=
    SingularClosure.fullTransportPressure_periodic c
  have hgradcoeff : SingularClosure.datumFourierCoeff (gradient p) =
      SingularClosure.datumFourierCoeff (gradient (SingularClosure.fullTransportPressure c)) := by
    exact (physical_pressure_gradient_coeff ν v d p
      hv hvper hdivv hd hdper hdivd hp hpper hmom).trans
      (SingularClosure.fullTransportPressure_gradient_coeff c hall hreal hsol).symm
  have hgrad : gradient p = gradient (SingularClosure.fullTransportPressure c) :=
    SingularClosure.datumFourierCoeff_injective_continuous_periodic
      (gradient p) (gradient (SingularClosure.fullTransportPressure c))
      (gradient_smooth hp).continuous (gradient_smooth hq).continuous
      (gradient_periodic hpper) (gradient_periodic hqper) hgradcoeff
  exact originNormalize_eq_of_gradient_eq
    (hp.differentiable (by simp)) (hq.differentiable (by simp)) hgrad

theorem pressureGradient_neg (p : ScalarField) : gradient (-p) = -gradient p := by
  funext x
  apply PiLp.ext
  intro i
  change fderiv ℝ (fun y => -p y) x (unitVector i) =
    -(fderiv ℝ p x (unitVector i))
  simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply]

theorem normalizedQuadraticPressure_eq_fullTransportPressure
    (v : Field) (hv : ContDiff ℝ ∞ v) (hvper : SpatialPeriodic v)
    (hdivv : ∀ x, divergence v x = 0) :
    normalizedQuadraticPressure v =
      normalizedFullTransportPressure (physicalFourierValue 0 v) := by
  let b : Field := convection v
  let d : Field := -leray b
  let p : ScalarField := quadraticPoissonPressure v
  have hb : ContDiff ℝ ∞ b := NSEMaxwell.PeriodicIntegration.convection_smooth hv
  have hbper : SpatialPeriodic b := SingularClosure.convection_periodic v hvper
  have hpform : p = -poissonInverse (divergence b) := by
    dsimp [p, quadraticPoissonPressure]
    rw [quadraticPressureSource_eq_neg_divergence_convection hv (funext hdivv)]
    exact Assembly.poissonInverse_neg_native (divergence b)
  have hp : ContDiff ℝ ∞ p := by
    rw [hpform]
    exact (Assembly.poissonInverse_smooth _ (Assembly.divergence_smooth b hb)
      (divergence_periodic hbper)).neg
  have hpper : SpatialPeriodic p := poissonInverse_periodic _
  have hd : ContDiff ℝ ∞ d := (Assembly.leray_smooth b hb hbper).neg
  have hdper : SpatialPeriodic d := by
    intro x i
    change -leray b (x + unitVector i) = -leray b x
    rw [leray_periodic hbper x i]
  have hdivd : ∀ x, divergence d x = 0 := by
    have heq : divergence d = 0 := by
      change divergence (-leray b) = 0
      rw [divergence_neg_native, Assembly.divergence_leray_zero b hb hbper, neg_zero]
    exact fun x => congrFun heq x
  have hmom : ∀ x, d x + convection v x + gradient p x = (0 : ℝ) • laplacian v x := by
    intro x
    rw [hpform, pressureGradient_neg]
    change -(b x - gradient (poissonInverse (divergence b)) x) + b x +
      -gradient (poissonInverse (divergence b)) x = (0 : ℝ) • laplacian v x
    rw [zero_smul]
    abel
  exact normalized_pressure_eq_fullTransportPressure 0 v d p
    hv hvper hdivv hd hdper hdivd hp hpper hmom

theorem nssolution_normalized_pressure_eq_fullTransportPressure
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p) {t : ℝ} (ht : 0 ≤ t) :
    originNormalize p t = fun x =>
      SingularClosure.fullTransportPressure (physicalFourierValue 0 (u t)) x -
      SingularClosure.fullTransportPressure (physicalFourierValue 0 (u t)) 0 := by
  rw [nssolution_normalized_pressure_eq_quadraticPoisson h ht]
  exact normalizedQuadraticPressure_eq_fullTransportPressure (u t)
    (NSEMaxwell.Classical.velocity_slice_smooth h.velocity_smooth ht)
    (h.velocity_periodic t ht) (h.divergence_free t ht)

theorem positiveAnalyticNSE_normalized_pressure_eq_fullTransportPressure
    {ν : ℝ} {u : Velocity} {p : Pressure}
    (h : PositiveAnalyticNSE ν u p) {t : ℝ} (ht : 0 < t) :
    originNormalize p t = fun x =>
      SingularClosure.fullTransportPressure (physicalFourierValue 0 (u t)) x -
      SingularClosure.fullTransportPressure (physicalFourierValue 0 (u t)) 0 := by
  rw [positiveAnalyticNSE_normalized_pressure_eq_quadraticPoisson h ht]
  exact normalizedQuadraticPressure_eq_fullTransportPressure (u t)
    (Assembly.analyticOnNhd_slab_slice_smooth h.velocity_analytic ht)
    (h.velocity_periodic t ht) (h.divergence_free t ht)

theorem PositiveTimeProfile.pressure_eq_fullTransportPressure
    {ν : ℝ} {a : Field} (p : PositiveTimeProfile ν a) (t : PositiveTime) :
    p.pressure t = normalizedFullTransportPressure (physicalFourierValue 0 (p.velocity t)) := by
  refine Quotient.inductionOn p ?_
  intro r
  change r.pressure t.val = normalizedFullTransportPressure (physicalFourierValue 0 (r.velocity t.val))
  have hpressure := positiveAnalyticNSE_normalized_pressure_eq_fullTransportPressure
    r.solution t.property
  calc
    r.pressure t.val = originNormalize r.pressure t.val := by
      funext x
      simp only [originNormalize, r.origin_normalized t, sub_zero]
    _ = _ := hpressure

end
end NSEGR.Strengthening
