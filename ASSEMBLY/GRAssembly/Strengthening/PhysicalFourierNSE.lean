import GRAssembly.Strengthening.PhysicalFourier
import SingularClosure.FourierProduct
import SingularClosure.FourierSobolevRhs
import SingularClosure.PeriodicFourierInjective
import FourierHodgeLaws.PoissonFromCoefficients

/-!
# Exact physical NSE to the native Sobolev vector field

Every Fourier coefficient is the actual cube integral. Spatial integration by
parts identifies the Laplacian and gradient. Actual Fourier synthesis and the
untruncated product theorem identify convection. Modewise Leray projection
eliminates the periodic pressure. No velocity mean condition is used.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SingularClosure
open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.HodgeProof

namespace NSEGR.Strengthening
noncomputable section

/-- The native integration-by-parts proof requires no velocity mean condition. -/
theorem datumFourierCoeff_solenoidal_of_divergence_free
    (a : SingularClosure.Field) (ha : ContDiff ℝ ∞ a)
    (hp : SingularClosure.SpatialPeriodic a)
    (hdiv : ∀ x, SingularClosure.divergence a x = 0) :
    SpectralSolenoidal (datumFourierCoeff a) := by
  intro k
  have hzero := integral_unitCube_divergence_eq_zero
    (fun i => datumFourierIntegrand a k i)
    (fun i => datumFourierIntegrand_contDiff ha k i)
    (fun i x => datumFourierIntegrand_periodic hp k i x i)
  have hsum (x : SingularClosure.Vec) :
      (∑ i : Fin 3, fderiv ℝ (datumFourierIntegrand a k i) x (SingularClosure.unitVector i)) =
        -(∑ i : Fin 3, derivativeSymbol i k * datumFourierIntegrand a k i x) := by
    simp_rw [datumFourierIntegrand_coordinateDerivative (ha.differentiable (by simp))]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum]
    change star (fourierCharacter k x) * (SingularClosure.divergence a x : ℂ) - _ = _
    rw [hdiv x]
    simp
  simp_rw [hsum] at hzero
  rw [integral_neg] at hzero
  have hcoeff : (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff a k i) = 0 := by
    have h := neg_eq_zero.mp hzero
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (datumFourierIntegrand_integrableOn ha.continuous k i).const_mul (derivativeSymbol i k))] at h
    simpa only [integral_const_mul, datumFourierCoeff] using h
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hfactor :
      (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff a k i) =
        C * ∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff a k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast, C]
    ring
  have hC : C ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  rw [hfactor] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left hC

/-- Actual physical smooth periodic fields are their native Fourier synthesis. -/
theorem physicalFourier_synthesis_eq
    (a : SingularClosure.Field) (ha : ContDiff ℝ ∞ a)
    (hp : SingularClosure.SpatialPeriodic a) :
    smoothFourierSynthesis (datumFourierCoeff a) = a := by
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff a)
    (fun m => SMOOTH_DATUM_MEM_TORUS_SOBOLEV m a ha hp)
  exact datumFourierCoeff_injective_continuous_periodic
    (smoothFourierSynthesis (datumFourierCoeff a)) a
    (smoothFourierSynthesis_contDiff _ hr).continuous ha.continuous
    (smoothFourierSynthesis_periodic _) hp
    (datumFourierCoeff_smoothFourierSynthesis _ hr (datumFourierCoeff_reality a))

theorem physicalFourierValue_synthesis_eq
    (m : ℕ) (a : SingularClosure.Field) (ha : ContDiff ℝ ∞ a)
    (hp : SingularClosure.SpatialPeriodic a) :
    smoothFourierSynthesis (physicalFourierValue m a).val = a := by
  rw [physicalFourierValue_coeff m a ha hp]
  exact physicalFourier_synthesis_eq a ha hp

theorem physicalFourierValue_convection_coeff
    (a : SingularClosure.Field) (ha : ContDiff ℝ ∞ a)
    (hp : SingularClosure.SpatialPeriodic a)
    (hdiv : ∀ x, SingularClosure.divergence a x = 0) :
    datumFourierCoeff (SingularClosure.convection a) =
      fullTransportCoefficients (physicalFourierValue 0 a) := by
  have hc := physicalFourierValue_coeff 0 a ha hp
  have hall : ∀ s : ℕ,
      Memℓp (sobolevWeightedCoeff s (physicalFourierValue 0 a).val) 2 := by
    intro s
    rw [hc]
    exact SMOOTH_DATUM_MEM_TORUS_SOBOLEV s a ha hp
  have hr : SpectralReality (physicalFourierValue 0 a).val := by
    rw [hc]
    exact datumFourierCoeff_reality a
  have hs : SpectralSolenoidal (physicalFourierValue 0 a).val := by
    rw [hc]
    exact datumFourierCoeff_solenoidal_of_divergence_free a ha hp hdiv
  have h := smoothFourierSynthesis_convection_coeff (physicalFourierValue 0 a) hall hr hs
  rw [physicalFourierValue_synthesis_eq 0 a ha hp] at h
  exact h

theorem datumFourierCoeff_real_smul (ν : ℝ) (a : SingularClosure.Field) :
    datumFourierCoeff (ν • a) = (ν : ℂ) • datumFourierCoeff a := by
  funext k i
  change (∫ x in SingularClosure.unitCube,
      star (fourierCharacter k x) * ((ν * a x i : ℝ) : ℂ)) =
    (ν : ℂ) * ∫ x in SingularClosure.unitCube,
      star (fourierCharacter k x) * (a x i : ℂ)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by rw [Complex.ofReal_mul]; ring)

theorem datumFourierCoeff_gradient_component
    (p : SingularClosure.Vec → ℝ) (hp : ContDiff ℝ ∞ p)
    (hpp : SingularClosure.SpatialPeriodic p) (k : Frequency) (i : Fin 3) :
    datumFourierCoeff (SingularClosure.gradient p) k i =
      derivativeSymbol i k * scalarCoeff p k := by
  exact scalarCoeff_coordinateDerivative p hp hpp i k

theorem coefficientLeray_derivativeSymbol (k : Frequency) (z : ℂ) :
    coefficientLeray k (fun i => derivativeSymbol i k * z) = 0 := by
  by_cases hk : k = 0
  · subst k
    funext i
    simp [coefficientLeray, derivativeSymbol]
  · have hden := frequency_complex_square_sum_ne_zero k hk
    have hsum : (∑ j : Fin 3, (k j : ℂ) * (derivativeSymbol j k * z)) =
        (2 * (Real.pi : ℂ) * Complex.I * z) * ∑ j : Fin 3, (k j : ℂ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_intCast]
      ring
    funext i
    simp only [coefficientLeray, if_neg hk, hsum, Pi.zero_apply, derivativeSymbol,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
    field_simp [hden]
    ring

theorem fourierLeray_gradient_zero
    (p : SingularClosure.Vec → ℝ) (hp : ContDiff ℝ ∞ p)
    (hpp : SingularClosure.SpatialPeriodic p) :
    fourierLerayLinear (datumFourierCoeff (SingularClosure.gradient p)) = 0 := by
  funext k i
  have hcoeff : datumFourierCoeff (SingularClosure.gradient p) k =
      fun j => derivativeSymbol j k * scalarCoeff p k := by
    funext j
    exact datumFourierCoeff_gradient_component p hp hpp k j
  change coefficientLeray k (datumFourierCoeff (SingularClosure.gradient p) k) i = 0
  rw [hcoeff, coefficientLeray_derivativeSymbol]
  rfl

theorem fourierLeray_eq_of_solenoidal (c : FourierCoeff) (hc : SpectralSolenoidal c) :
    fourierLerayLinear c = c := by
  funext k i
  exact congrFun (coefficientLeray_eq_of_solenoidal k (c k) (hc k)) i

theorem laplacianCoefficient_solenoidal (c : FourierCoeff) (hc : SpectralSolenoidal c) :
    SpectralSolenoidal (laplacianCoefficient c) := by
  intro k
  change (∑ i : Fin 3, (k i : ℂ) * (-(laplacianFrequency k : ℂ) * c k i)) = 0
  calc
    _ = -(laplacianFrequency k : ℂ) * ∑ i : Fin 3, (k i : ℂ) * c k i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hc k, mul_zero]

/-- The literal physical momentum equation gives the full untruncated Fourier equation. -/
theorem physical_momentum_fullFourierRhs
    (ν : ℝ) (a d : SingularClosure.Field) (p : SingularClosure.Vec → ℝ)
    (ha : ContDiff ℝ ∞ a) (hpa : SingularClosure.SpatialPeriodic a)
    (hdiva : ∀ x, SingularClosure.divergence a x = 0)
    (hd : ContDiff ℝ ∞ d) (hpd : SingularClosure.SpatialPeriodic d)
    (hdivd : ∀ x, SingularClosure.divergence d x = 0)
    (hp : ContDiff ℝ ∞ p) (hpp : SingularClosure.SpatialPeriodic p)
    (heq : ∀ x, d x + SingularClosure.convection a x + SingularClosure.gradient p x =
      ν • SingularClosure.laplacian a x) :
    datumFourierCoeff d = fullFourierRhs ν (physicalFourierValue 0 a) := by
  have hc : Continuous (SingularClosure.convection a) := (convection_contDiff a ha).continuous
  have hg : Continuous (SingularClosure.gradient p) :=
    (NSEMaxwell.PeriodicIntegration.gradient_smooth hp).continuous
  have he : d + SingularClosure.convection a + SingularClosure.gradient p =
      ν • SingularClosure.laplacian a := funext heq
  have hf := congrArg datumFourierCoeff he
  rw [datumFourierCoeff_add (d + SingularClosure.convection a) (SingularClosure.gradient p)
      (hd.continuous.add hc) hg,
    datumFourierCoeff_add d (SingularClosure.convection a) hd.continuous hc,
    datumFourierCoeff_real_smul,
    datumFourierCoeff_laplacian a ha hpa,
    physicalFourierValue_convection_coeff a ha hpa hdiva] at hf
  have h := congrArg fourierLerayLinear hf
  rw [map_add, map_add, map_smul,
    fourierLeray_gradient_zero p hp hpp,
    fourierLeray_eq_of_solenoidal (datumFourierCoeff d)
      (datumFourierCoeff_solenoidal_of_divergence_free d hd hpd hdivd),
    fourierLeray_eq_of_solenoidal (laplacianCoefficient (datumFourierCoeff a))
      (laplacianCoefficient_solenoidal _
        (datumFourierCoeff_solenoidal_of_divergence_free a ha hpa hdiva)), add_zero] at h
  have hdf := eq_sub_iff_add_eq.mpr h
  funext k i
  have hki := congrFun (congrFun hdf k) i
  change datumFourierCoeff d k i =
    (ν : ℂ) * (-(laplacianFrequency k : ℂ) * datumFourierCoeff a k i) -
      coefficientLeray k (fullTransportCoefficients (physicalFourierValue 0 a) k) i at hki
  rw [hki]
  unfold fullFourierRhs
  rw [physicalFourierValue_coeff 0 a ha hpa]
  change (ν : ℂ) * (-(laplacianFrequency k : ℂ) * datumFourierCoeff a k i) -
      coefficientLeray k (fullTransportCoefficients (physicalFourierValue 0 a) k) i =
    -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
        datumFourierCoeff a k i -
      coefficientLeray k (fullTransportCoefficients (physicalFourierValue 0 a) k) i
  simp only [laplacianFrequency, Complex.ofReal_mul]
  ring

/-- The momentum coefficient identity is equality in the actual Sobolev space. -/
theorem physical_momentum_fourierSobolevRhs
    (ν : ℝ) (a d : SingularClosure.Field) (p : SingularClosure.Vec → ℝ)
    (ha : ContDiff ℝ ∞ a) (hpa : SingularClosure.SpatialPeriodic a)
    (hdiva : ∀ x, SingularClosure.divergence a x = 0)
    (hd : ContDiff ℝ ∞ d) (hpd : SingularClosure.SpatialPeriodic d)
    (hdivd : ∀ x, SingularClosure.divergence d x = 0)
    (hp : ContDiff ℝ ∞ p) (hpp : SingularClosure.SpatialPeriodic p)
    (heq : ∀ x, d x + SingularClosure.convection a x + SingularClosure.gradient p x =
      ν • SingularClosure.laplacian a x) (m : ℕ) :
    physicalFourierValue m d = fourierSobolevRhs ν m (physicalFourierValue (m + 2) a) := by
  apply Subtype.ext
  rw [physicalFourierValue_coeff m d hd hpd, fourierSobolevRhs_coefficient_eq_fullRhs]
  have hlower : torusSobolevLower 0 (m + 2) (Nat.zero_le _) (physicalFourierValue (m + 2) a) =
      physicalFourierValue 0 a := by
    apply Subtype.ext
    rw [torusSobolevLower_coeff, physicalFourierValue_coeff (m + 2) a ha hpa,
      physicalFourierValue_coeff 0 a ha hpa]
  rw [hlower]
  exact physical_momentum_fullFourierRhs ν a d p ha hpa hdiva hd hpd hdivd hp hpp heq

/-- Positive-time incompressibility differentiates to the actual time derivative field. -/
theorem positive_timeDerivative_slice_properties
    (u : NSEMaxwell.Classical.Velocity)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × NSEMaxwell.Classical.Vec => u z.1 z.2)
      {z | 0 < z.1})
    (hp : ∀ s : ℝ, 0 < s → SingularClosure.SpatialPeriodic (u s))
    (hdiv : ∀ s : ℝ, 0 < s → ∀ x, SingularClosure.divergence (u s) x = 0)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (NSEMaxwell.Classical.timeDerivative u t) ∧
      SingularClosure.SpatialPeriodic (NSEMaxwell.Classical.timeDerivative u t) ∧
      (∀ x, SingularClosure.divergence (NSEMaxwell.Classical.timeDerivative u t) x = 0) := by
  let c : ℝ := t / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have htc : 0 < t - c := by dsimp [c]; linarith
  let v : NSEMaxwell.Classical.Velocity := fun s x => u (s + c) x
  have hv : SmoothVelocity v := by
    have hg : ContDiffOn ℝ ∞
        (fun z : ℝ × NSEMaxwell.Classical.Vec => (z.1 + c, z.2))
        NSEMaxwell.Classical.forwardSpacetime :=
      ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    exact hu.comp (s := NSEMaxwell.Classical.forwardSpacetime) hg
      (fun z hz => add_pos_of_nonneg_of_pos hz hc)
  have hpv : PeriodicVelocity v := by
    intro s hs
    exact hp (s + c) (add_pos_of_nonneg_of_pos hs hc)
  have hdivv : ∀ s : ℝ, 0 ≤ s → ∀ x, NSEMaxwell.Classical.divergence (v s) x = 0 := by
    intro s hs x
    exact hdiv (s + c) (add_pos_of_nonneg_of_pos hs hc) x
  have hshift : HasDerivAt (fun s : ℝ => s - c) 1 t :=
    (hasDerivAt_id t).sub_const c
  have hdt : NSEMaxwell.Classical.timeDerivative v (t - c) =
      NSEMaxwell.Classical.timeDerivative u t := by
    funext x
    have hbase := (time_slice_hasDerivWithinAt hv htc.le x).hasDerivAt (Ici_mem_nhds htc)
    have h := hbase.scomp t hshift
    have he : HasDerivAt (fun s : ℝ => u s x)
        (NSEMaxwell.Classical.timeDerivative v (t - c) x) t := by
      simpa only [Function.comp_def, v, sub_add_cancel, one_smul] using h
    exact (he.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht.le)).symm
  rw [← hdt]
  exact ⟨velocity_slice_smooth (timeDerivative_smooth hv) htc.le,
    timeDerivative_periodic hpv (t - c) htc.le,
    fun x => timeDerivative_divergence_zero hv hdivv htc.le x⟩

/-- Exact G30: actual positive-time NSE implies the literal Sobolev norm differential equation. -/
theorem physical_NSE_fourierSobolev_hasDerivAt
    (ν : ℝ) (u : NSEMaxwell.Classical.Velocity) (p : NSEMaxwell.Classical.Pressure)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × NSEMaxwell.Classical.Vec => u z.1 z.2)
      {z | 0 < z.1})
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × NSEMaxwell.Classical.Vec => p z.1 z.2)
      {z | 0 < z.1})
    (hpu : ∀ s : ℝ, 0 < s → SingularClosure.SpatialPeriodic (u s))
    (hpp : ∀ s : ℝ, 0 < s → SingularClosure.SpatialPeriodic (p s))
    (hdiv : ∀ s : ℝ, 0 < s → ∀ x, SingularClosure.divergence (u s) x = 0)
    (heq : ∀ s : ℝ, 0 < s → ∀ x,
      NSEMaxwell.Classical.timeDerivative u s x + SingularClosure.convection (u s) x +
        SingularClosure.gradient (p s) x = ν • SingularClosure.laplacian (u s) x)
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (physicalFourierCurve m u)
      (fourierSobolevRhs ν m (physicalFourierCurve (m + 2) u t)) t := by
  have hua : ContDiff ℝ ∞ (u t) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ht)
  have hpa : ContDiff ℝ ∞ (p t) :=
    hp.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ht)
  obtain ⟨hd, hpd, hdivd⟩ := positive_timeDerivative_slice_properties u hu hpu hdiv ht
  apply (physicalFourierCurve_hasDerivAt_of_positive_smooth u hu hpu m ht).congr_deriv
  exact physical_momentum_fourierSobolevRhs ν (u t) (NSEMaxwell.Classical.timeDerivative u t)
    (p t) hua (hpu t ht) (hdiv t ht) hd hpd hdivd hpa (hpp t ht) (heq t ht) m

end
end NSEGR.Strengthening
