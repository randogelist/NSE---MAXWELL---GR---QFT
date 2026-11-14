import GRAssembly.Strengthening.PositiveProfiles
import GRAssembly.NativeCalculus
import GRAssembly.HodgeTransport
import NSEMaxwell.PeriodicIntegration

/-!
The literal native quadratic Poisson pressure, with the constant pressure mode
fixed at the spatial origin. The velocity zero mode is unrestricted.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff BigOperators

namespace NSEGR.Strengthening
noncomputable section

def quadraticPressureSource (v : Field) : ScalarField :=
  -divergence (tensorDivergence (fun x => velocityOuter (v x)))

def quadraticPoissonPressure (v : Field) : ScalarField :=
  poissonInverse (quadraticPressureSource v)

def normalizedQuadraticPressure (v : Field) : ScalarField :=
  fun x => quadraticPoissonPressure v x - quadraticPoissonPressure v 0

@[simp]
theorem normalizedQuadraticPressure_zero (v : Field) :
    normalizedQuadraticPressure v 0 = 0 := by
  simp [normalizedQuadraticPressure]

theorem divergence_add_smooth {v w : Field}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    divergence (v + w) = divergence v + divergence w := by
  funext x
  change (∑ i : Fin 3,
    (fderiv ℝ (fun y => v y + w y) x (unitVector i)) i) = _
  rw [fderiv_fun_add (hv.differentiable (by simp) x)
    (hw.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]
  rfl

theorem divergence_smul_smooth (c : ℝ) {v : Field}
    (hv : ContDiff ℝ ∞ v) : divergence (c • v) = c • divergence v := by
  funext x
  change (∑ i : Fin 3,
    (fderiv ℝ (fun y => c • v y) x (unitVector i)) i) =
      c • (∑ i : Fin 3, (fderiv ℝ v x (unitVector i)) i)
  rw [fderiv_fun_const_smul (hv.differentiable (by simp) x) c]
  simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    Finset.smul_sum]

theorem divergence_neg_native (v : Field) :
    divergence (-v) = -divergence v := by
  funext x
  change (∑ i : Fin 3, (fderiv ℝ (fun y => -v y) x (unitVector i)) i) =
    -(∑ i : Fin 3, (fderiv ℝ v x (unitVector i)) i)
  simp only [fderiv_fun_neg,
    ContinuousLinearMap.neg_apply, PiLp.neg_apply, Finset.sum_neg_distrib]

theorem divergence_laplacian_zero {v : Field}
    (hv : ContDiff ℝ ∞ v) (hdiv : divergence v = 0) :
    divergence (laplacian v) = 0 := by
  have hcurl : NSEMaxwell.Classical.spatialCurl
      (NSEMaxwell.Classical.spatialCurl v) = -laplacian v :=
    NSEMaxwell.CurlCurl.curl_curl_of_divergence_zero hv hdiv
  have hzero : divergence (NSEMaxwell.Classical.spatialCurl
      (NSEMaxwell.Classical.spatialCurl v)) = 0 :=
    NSEMaxwell.CurlCurl.divergence_curl (NSEMaxwell.CurlCurl.spatialCurl_smooth hv)
  rw [hcurl, divergence_neg_native] at hzero
  exact neg_eq_zero.mp hzero

theorem quadraticPressureSource_eq_neg_divergence_convection {v : Field}
    (hv : ContDiff ℝ ∞ v) (hdiv : divergence v = 0) :
    quadraticPressureSource v = -divergence (convection v) := by
  have htransport : tensorDivergence (fun x => velocityOuter (v x)) = convection v := by
    funext x
    exact tensorDivergence_velocityOuter_of_divergence_zero
      (hv.differentiable (by simp) x) (congrFun hdiv x)
  rw [quadraticPressureSource, htransport]

theorem pressure_poisson_of_divergence_free_momentum
    {ν : ℝ} {v d : Field} {p : ScalarField}
    (hv : ContDiff ℝ ∞ v) (hd : ContDiff ℝ ∞ d) (hp : ContDiff ℝ ∞ p)
    (hdiv : divergence v = 0) (hdivd : divergence d = 0)
    (hmom : d + convection v + gradient p = ν • laplacian v) :
    scalarLaplacian p = quadraticPressureSource v := by
  have hconv : ContDiff ℝ ∞ (convection v) :=
    NSEMaxwell.PeriodicIntegration.convection_smooth hv
  have hlap : ContDiff ℝ ∞ (laplacian v) :=
    NSEMaxwell.PeriodicIntegration.laplacian_smooth hv
  have hdconv : ContDiff ℝ ∞ (d + convection v) := hd.add hconv
  have he := congrArg divergence hmom
  rw [divergence_add_smooth (v := d + convection v) (w := gradient p)
      hdconv (gradient_smooth hp),
    divergence_add_smooth (v := d) (w := convection v) hd hconv, hdivd, zero_add,
    divergence_gradient hp, divergence_smul_smooth ν hlap,
    divergence_laplacian_zero hv hdiv, smul_zero] at he
  rw [quadraticPressureSource_eq_neg_divergence_convection hv hdiv]
  funext x
  have hx := congrFun he x
  change divergence (convection v) x + scalarLaplacian p x = 0 at hx
  change scalarLaplacian p x = -divergence (convection v) x
  linarith

theorem quadraticPoissonPressure_eq_pressure_sub_mean
    {ν : ℝ} {v d : Field} {p : ScalarField}
    (hv : ContDiff ℝ ∞ v) (hd : ContDiff ℝ ∞ d) (hp : ContDiff ℝ ∞ p)
    (hpper : SpatialPeriodic p)
    (hdiv : divergence v = 0) (hdivd : divergence d = 0)
    (hmom : d + convection v + gradient p = ν • laplacian v) :
    quadraticPoissonPressure v = p - (fun _ => scalarMean p) := by
  rw [quadraticPoissonPressure,
    ← pressure_poisson_of_divergence_free_momentum hv hd hp hdiv hdivd hmom]
  exact Assembly.poissonInverse_scalarLaplacian p hp hpper

theorem normalized_pressure_eq_quadraticPoisson
    {ν : ℝ} {v d : Field} {p : ScalarField}
    (hv : ContDiff ℝ ∞ v) (hd : ContDiff ℝ ∞ d) (hp : ContDiff ℝ ∞ p)
    (hpper : SpatialPeriodic p)
    (hdiv : divergence v = 0) (hdivd : divergence d = 0)
    (hmom : d + convection v + gradient p = ν • laplacian v) :
    (fun x => p x - p 0) = normalizedQuadraticPressure v := by
  have hpressure := quadraticPoissonPressure_eq_pressure_sub_mean
    hv hd hp hpper hdiv hdivd hmom
  funext x
  rw [normalizedQuadraticPressure, hpressure]
  simp only [Pi.sub_apply]
  ring

theorem nssolution_normalized_pressure_eq_quadraticPoisson
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSEMaxwell.Classical.NSSolution ν a u p)
    {t : ℝ} (ht : 0 ≤ t) :
    originNormalize p t = normalizedQuadraticPressure (u t) := by
  apply normalized_pressure_eq_quadraticPoisson
    (ν := ν) (d := NSEMaxwell.Classical.timeDerivative u t)
  · exact NSEMaxwell.Classical.velocity_slice_smooth h.velocity_smooth ht
  · exact NSEMaxwell.Classical.velocity_slice_smooth
      (NSEMaxwell.Spacetime.timeDerivative_smooth h.velocity_smooth) ht
  · exact NSEMaxwell.Classical.pressure_slice_smooth h.pressure_smooth ht
  · exact h.pressure_periodic t ht
  · exact funext (h.divergence_free t ht)
  · exact funext (NSEMaxwell.Spacetime.timeDerivative_divergence_zero
      h.velocity_smooth h.divergence_free ht)
  · exact funext (h.equation t ht)

theorem localNSE_localTimeDerivative_smooth
    {ν τ δ : ℝ} {u : Velocity} {p : Pressure}
    (h : LocalNSE ν τ δ u p) {t : ℝ} (ht : t ∈ timeInterval τ δ) :
    ContDiff ℝ ∞ (localTimeDerivative u t) := by
  apply (contDiff_piLp 2).mpr
  intro i
  have heq : (fun x => localTimeDerivative u t x i) =
      (fun x => Assembly.jointTime (fun z : ℝ × Vec => u z.1 z.2 i) (t, x)) := by
    funext x
    exact (Assembly.velocity_coordinate_timeDerivative (h.velocity_analytic (t, x) ht) i).symm
  rw [heq]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hc : AnalyticAt ℝ (fun z : ℝ × Vec => u z.1 z.2 i) (t, x) := by
    let pr : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
    change AnalyticAt ℝ (fun z : ℝ × Vec => pr (u z.1 z.2)) (t, x)
    exact (pr.analyticAt (u t x)).comp_of_eq (h.velocity_analytic (t, x) ht) rfl
  exact ((Assembly.analyticAt_jointTime hc).comp
    (analyticAt_const.prod analyticAt_id)).contDiffAt

theorem localNSE_divergence_localTimeDerivative_zero
    {ν τ δ : ℝ} {u : Velocity} {p : Pressure}
    (h : LocalNSE ν τ δ u p) {t : ℝ} (ht : t ∈ timeInterval τ δ) :
    divergence (localTimeDerivative u t) = 0 := by
  let f : Fin 3 → ℝ × Vec → ℝ := fun i z => u z.1 z.2 i
  have hf (i : Fin 3) (x : Vec) : AnalyticAt ℝ (f i) (t, x) := by
    let pr : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
    change AnalyticAt ℝ (fun z : ℝ × Vec => pr (u z.1 z.2)) (t, x)
    exact (pr.analyticAt (u t x)).comp_of_eq (h.velocity_analytic (t, x) ht) rfl
  have hdt := localNSE_localTimeDerivative_smooth h ht
  have htime (i : Fin 3) :
      (fun x => localTimeDerivative u t x i) =
        (fun x => Assembly.jointTime (f i) (t, x)) := by
    funext x
    exact (Assembly.velocity_coordinate_timeDerivative (h.velocity_analytic (t, x) ht) i).symm
  have hspace (s : ℝ) (hs : s ∈ timeInterval τ δ) (x : Vec) (i : Fin 3) :
      Assembly.jointSpace (f i) i (s, x) = spatialPartial (u s) i x i :=
    StressCalc.component_fderiv
      ((Assembly.analyticOnNhd_slab_slice_smooth h.velocity_analytic hs).differentiable
        (by simp) x) (unitVector i) i
  funext x
  have hsum : divergence (localTimeDerivative u t) x =
      Assembly.jointTime (fun z => ∑ i : Fin 3, Assembly.jointSpace (f i) i z) (t, x) := by
    rw [Assembly.jointTime_sum Finset.univ
      (fun i _ => Assembly.analyticAt_jointSpace (hf i x) i)]
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    calc
      spatialPartial (localTimeDerivative u t) i x i =
          fderiv ℝ (fun y => localTimeDerivative u t y i) x (unitVector i) :=
        (StressCalc.component_fderiv (hdt.differentiable (by simp) x) (unitVector i) i).symm
      _ = Assembly.jointSpace (Assembly.jointTime (f i)) i (t, x) := by
        rw [htime i]
        rfl
      _ = Assembly.jointTime (Assembly.jointSpace (f i) i) (t, x) :=
        (Assembly.jointTime_jointSpace (hf i x) i).symm
  rw [hsum]
  have hz : (fun s => ∑ i : Fin 3, Assembly.jointSpace (f i) i (s, x)) =ᶠ[𝓝 t]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simp_rw [hspace s hs x]
    exact h.divergence_free s hs x
  exact hz.deriv_eq.trans (deriv_const t 0)

theorem localNSE_normalized_pressure_eq_quadraticPoisson
    {ν τ δ : ℝ} {u : Velocity} {p : Pressure}
    (h : LocalNSE ν τ δ u p) {t : ℝ} (ht : t ∈ timeInterval τ δ) :
    originNormalize p t = normalizedQuadraticPressure (u t) := by
  apply normalized_pressure_eq_quadraticPoisson
    (ν := ν) (d := localTimeDerivative u t)
  · exact Assembly.analyticOnNhd_slab_slice_smooth h.velocity_analytic ht
  · exact localNSE_localTimeDerivative_smooth h ht
  · exact Assembly.analyticOnNhd_slab_slice_smooth h.pressure_analytic ht
  · exact h.periodic_pressure t ht
  · exact funext (h.divergence_free t ht)
  · exact localNSE_divergence_localTimeDerivative_zero h ht
  · funext x
    exact sub_eq_zero.mp (h.momentum t ht x)

theorem positiveAnalyticNSE_normalized_pressure_eq_quadraticPoisson
    {ν : ℝ} {u : Velocity} {p : Pressure}
    (h : PositiveAnalyticNSE ν u p) {t : ℝ} (ht : 0 < t) :
    originNormalize p t = normalizedQuadraticPressure (u t) := by
  apply localNSE_normalized_pressure_eq_quadraticPoisson
    (positiveTimeNSERepresentative h t ht).solution
  change t - t / 2 < t ∧ t < t + t / 2
  constructor <;> linarith

theorem PositiveTimeProfile.pressure_eq_quadraticPoisson
    {ν : ℝ} {a : Field} (p : PositiveTimeProfile ν a) (t : PositiveTime) :
    p.pressure t = normalizedQuadraticPressure (p.velocity t) := by
  refine Quotient.inductionOn p ?_
  intro r
  have hp := positiveAnalyticNSE_normalized_pressure_eq_quadraticPoisson
    r.solution t.property
  change r.pressure t.val = normalizedQuadraticPressure (r.velocity t.val)
  calc
    r.pressure t.val = originNormalize r.pressure t.val := by
      funext x
      simp only [originNormalize, r.origin_normalized t, sub_zero]
    _ = _ := hp

theorem nseGerm_pressure_eq_quadraticPoisson
    {ν t0 : ℝ} (n : NSEgerm ν t0) :
    NSEgerm.originPressureAtCenter n =
      normalizedQuadraticPressure (NSEgerm.velocityAtCenter n) := by
  refine Quotient.inductionOn n ?_
  intro r
  change originNormalize r.pressure t0 = normalizedQuadraticPressure (r.velocity t0)
  apply localNSE_normalized_pressure_eq_quadraticPoisson r.solution
  change t0 - r.radius < t0 ∧ t0 < t0 + r.radius
  constructor <;> linarith [r.solution.radius_pos]

theorem nseFamilyPressure_eq_quadraticPoisson
    {ν : ℝ} (η : PositiveTimeNSEGermFamily ν) (t : PositiveTime) :
    nseFamilyPressure η t = normalizedQuadraticPressure (nseFamilyVelocity η t) :=
  nseGerm_pressure_eq_quadraticPoisson (η t)

theorem decodedGRFamily_pressure_eq_quadraticPoisson
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (γ : PositiveTimeGRGermFamily ν ρ)
    (t : PositiveTime) :
    nseFamilyPressure (decodeGRFamily ν ρ hρ γ) t =
      normalizedQuadraticPressure (grFamilyVelocity γ t) := by
  rw [nseFamilyPressure_eq_quadraticPoisson, decodeGRFamily_velocity]

end
end NSEGR.Strengthening
