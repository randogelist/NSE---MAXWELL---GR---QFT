import QuantumAdapter.Obligations.NativeContinuum
import QuantumAdapter.Obligations.GalerkinContinuumPressure
import QuantumAdapter.Obligations.GalerkinPhysicalFourier

/-!
# The exact native reverse Galerkin implication

All seven NSSolution fields are constructed from the actual coefficient limit.
The only analytic input is the original all-horizon uniform Galerkin H3 bound.
No unconditional Navier--Stokes regularity assertion is made.
-/
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations
open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (Data NSSolution SmoothVelocity)
noncomputable section

theorem infiniteTransport_eq_fullTransportCoefficients (c : TorusSobolev 0) :
    infiniteTransport c.val = fullTransportCoefficients c := by
  funext k i
  exact (divergenceTransportCoefficient_apply k i c c).symm

theorem gradient_contDiff_of_contDiff (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (SingularClosure.gradient p) := by
  apply (contDiff_piLp 2).2
  intro i
  exact (contDiff_infty_iff_fderiv.mp hp).2.clm_apply contDiff_const

theorem gradient_periodic_of_periodic (p : Vec → ℝ) (hp : SpatialPeriodic p) :
    SpatialPeriodic (SingularClosure.gradient p) := by
  intro x j
  have heq : (fun y : Vec => p (y + unitVector j)) = p := funext (fun y => hp y j)
  have hd := congrArg (fun f : Vec → ℝ => fderiv ℝ f x) heq
  have hfd : fderiv ℝ p (x + unitVector j) = fderiv ℝ p x := by
    simpa only [fderiv_comp_add_right] using hd
  ext i
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) hfd

theorem laplacian_contDiff_of_contDiff (a : Field) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (laplacian a) := by
  change ContDiff ℝ ∞ (fun x => ∑ j : Fin 3, iteratedCoordinateDerivative j 2 a x)
  exact ContDiff.sum (fun j _ => iteratedCoordinateDerivative_smooth j 2 a ha)

theorem laplacian_periodic_of_periodic (a : Field) (hp : SpatialPeriodic a) :
    SpatialPeriodic (laplacian a) := by
  intro x j
  change (∑ i : Fin 3, iteratedCoordinateDerivative i 2 a (x + unitVector j)) =
    ∑ i : Fin 3, iteratedCoordinateDerivative i 2 a x
  exact Finset.sum_congr rfl (fun i _ => iteratedCoordinateDerivative_spatialPeriodic i 2 a hp x j)

theorem spatialPeriodic_add_fields {a b : Field} (ha : SpatialPeriodic a) (hb : SpatialPeriodic b) :
    SpatialPeriodic (a + b) := by
  intro x j
  simp only [Pi.add_apply, ha x j, hb x j]

/-- Fourier uniqueness identifies the literal physical PDE, including its pressure and time trace. -/
theorem timeTower_native_equation
    (ν : ℝ) {d : ℕ → ℝ → FourierCoeff}
    (hd : FourierTimeTowerDerivative d) (hb : FourierTimeTowerBounds d)
    (hr : ∀ n t, 0 ≤ t → SpectralReality (d n t) ∧ SpectralSolenoidal (d n t))
    (t : ℝ) (ht : 0 ≤ t) (hevo : d 1 t = nativeFourierRhs ν (d 0 t)) (x : Vec) :
    timeDerivative (fun r => smoothFourierSynthesis (d 0 r)) t x +
        convection (smoothFourierSynthesis (d 0 t)) x +
        SingularClosure.gradient (physicalConvectionPressure (fun r => smoothFourierSynthesis (d 0 r)) t) x =
      ν • laplacian (smoothFourierSynthesis (d 0 t)) x := by
  let c : TorusSobolev 0 := ⟨d 0 t, hb.mem_sobolev 0 0 t ht⟩
  have hc (m : ℕ) : Memℓp (sobolevWeightedCoeff m c.val) 2 := hb.mem_sobolev 0 m t ht
  have hreal : SpectralReality c.val := (hr 0 t ht).1
  have hsol : SpectralSolenoidal c.val := (hr 0 t ht).2
  have hdata := smoothFourierSynthesis_timeTower_data_coefficients hb 0 t ht hreal hsol
  have hdata₁ := smoothFourierSynthesis_timeTower_data_coefficients hb 1 t ht
    (hr 1 t ht).1 (hr 1 t ht).2
  have hps := fullTransportPressure_contDiff c hc hreal hsol
  have hpp := fullTransportPressure_periodic c
  have hgc := (gradient_contDiff_of_contDiff _ hps).continuous
  have hgp := gradient_periodic_of_periodic _ hpp
  have hcc := (convection_contDiff _ hdata.1.smooth).continuous
  have hcp := convection_periodic _ hdata.1.periodic
  have hlc := (laplacian_contDiff_of_contDiff _ hdata.1.smooth).continuous
  have hlp := laplacian_periodic_of_periodic _ hdata.1.periodic
  have hfield : smoothFourierSynthesis (d 1 t) + convection (smoothFourierSynthesis (d 0 t)) +
      SingularClosure.gradient (fullTransportPressure c) = ν • laplacian (smoothFourierSynthesis (d 0 t)) := by
    apply datumFourierCoeff_injective_continuous_periodic _ _
      ((hdata₁.1.smooth.continuous.add hcc).add hgc) (hlc.const_smul ν)
      (spatialPeriodic_add_fields (spatialPeriodic_add_fields hdata₁.1.periodic hcp) hgp)
      (fun y j => by simp only [Pi.smul_apply, hlp y j])
    rw [datumFourierCoeff_add _ _ (hdata₁.1.smooth.continuous.add hcc) hgc,
      datumFourierCoeff_add _ _ hdata₁.1.smooth.continuous hcc,
      hdata₁.2, datumFourierCoeff_real_smul]
    have hconv : datumFourierCoeff (convection (smoothFourierSynthesis (d 0 t))) =
        fullTransportCoefficients c := smoothFourierSynthesis_convection_coeff c hc hreal hsol
    rw [hconv, fullTransportPressure_gradient_coeff c hc hreal hsol]
    funext k i
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [datumFourierCoeff_laplacian_apply _ hdata.1.smooth hdata.1.periodic, hdata.2]
    have hki : d 1 t k i = -((ν * laplaceSymbol k : ℝ) : ℂ) * d 0 t k i -
        coefficientLeray k (fullTransportCoefficients c k) i := by
      rw [hevo]
      change -((ν * laplaceSymbol k : ℝ) : ℂ) * d 0 t k i -
        coefficientLeray k (infiniteTransport c.val k) i = _
      rw [infiniteTransport_eq_fullTransportCoefficients]
    rw [hki]
    push_cast
    ring
  rw [timeDerivative_smoothFourierSynthesis_timeTower hd hb 0 t ht x,
    physicalConvectionPressure_eq_fullTransportPressure hb t ht hreal hsol]
  exact congrFun hfield x

/-- Deterministic assembly of the exact seven native NSSolution fields. -/
theorem timeTower_native_solution
    (ν : ℝ) (a : Field) (ha : Data a) (d : ℕ → ℝ → FourierCoeff)
    (hd : FourierTimeTowerDerivative d) (hb : FourierTimeTowerBounds d)
    (hr : ∀ n t, 0 ≤ t → SpectralReality (d n t) ∧ SpectralSolenoidal (d n t))
    (hzero : d 0 0 = datumFourierCoeff a)
    (hevo : ∀ t : ℝ, 0 ≤ t → d 1 t = nativeFourierRhs ν (d 0 t)) :
    NSSolution ν a (fun t => smoothFourierSynthesis (d 0 t))
      (physicalConvectionPressure (fun t => smoothFourierSynthesis (d 0 t))) := by
  have hu : SmoothVelocity (fun t => smoothFourierSynthesis (d 0 t)) :=
    smoothFourierSynthesis_timeTower_contDiffOn hd hb 0
  have hup : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (smoothFourierSynthesis (d 0 t)) :=
    fun t ht => smoothFourierSynthesis_periodic _
  refine ⟨hu, physicalConvectionPressure_smooth hu hup, hup,
    (fun t ht => physicalConvectionPressure_periodic _ t), ?_, ?_, ?_⟩
  · intro t ht
    exact (smoothFourierSynthesis_timeTower_data_coefficients hb 0 t ht
      (hr 0 t ht).1 (hr 0 t ht).2).1.divergence_free
  · intro t ht x
    exact timeTower_native_equation ν hd hb hr t ht (hevo t ht) x
  · exact smoothFourierSynthesis_timeTower_initial a ha hzero

/-- P7: all-horizon actual Galerkin H3 bounds yield an actual global native solution. -/
theorem phaseFlow_compactness {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : Field) (ha : Data a)
    (h3 : ∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T) :
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p := by
  obtain ⟨d, hd, hb, hr, hzero, hevo⟩ := native_continuum_tower_exists hν F a ha h3
  exact ⟨(fun t => smoothFourierSynthesis (d 0 t)),
    physicalConvectionPressure (fun t => smoothFourierSynthesis (d 0 t)),
    timeTower_native_solution ν a ha d hd hb hr hzero hevo⟩

end
end QuantumAdapter.Obligations
