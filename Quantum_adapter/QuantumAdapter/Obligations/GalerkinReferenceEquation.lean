import QuantumAdapter.Obligations.GalerkinReferenceTime
import QuantumAdapter.Obligations.GalerkinPhysicalFourier
import QuantumAdapter.Obligations.GalerkinTransport
import QuantumAdapter.Obligations.EnergyConvection
import SingularClosure.FourierProduct

/-!
# The exact projected coefficient equation of a native classical solution

The pressure is eliminated by its actual periodic gradient coefficient identity.
The solenoidal time derivative is obtained by differentiating the actual Fourier
constraint. The convection coefficient is identified with the existing bounded
bilinear H0 convolution through Fourier uniqueness.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly NSEMaxwell.Classical

noncomputable section

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- Actual reference coefficients in each native Sobolev space. -/
def referenceSobolevAt (h : NSSolution ν a u p) (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    TorusSobolev s :=
  ⟨datumFourierCoeff (u t), h.spatial_all_sobolev t ht s⟩

@[simp]
theorem referenceSobolevAt_coeff (h : NSSolution ν a u p) (s : ℕ)
    (t : ℝ) (ht : 0 ≤ t) : (referenceSobolevAt h s t ht).val = datumFourierCoeff (u t) := rfl

/-- The native pressure has a smooth spatial slice at every forward time. -/
theorem NSSolution.pressure_spatial_smooth (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (p t) := by
  simpa only [Function.comp_def] using h.pressure_smooth.comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ht)

/-- Smooth gradient slices justify the actual pressure Fourier integrals. -/
theorem NSSolution.pressure_gradient_continuous (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) : Continuous (gradient (p t)) := by
  have hs := h.pressure_spatial_smooth t ht
  have hg : ContDiff ℝ ∞ (gradient (p t)) := by
    apply (contDiff_piLp 2).2
    intro i
    exact (contDiff_infty_iff_fderiv.mp hs).2.clm_apply contDiff_const
  exact hg.continuous

/-- Fourier uniqueness turns the native smooth convection into its actual convolution. -/
theorem NSSolution.convection_fourier_eq (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) :
    datumFourierCoeff (convection (u t)) =
      fullTransportCoefficients (referenceSobolevAt h 0 t ht) := by
  have hc := smoothFourierSynthesis_convection_coeff (referenceSobolevAt h 0 t ht)
    (fun s => h.spatial_all_sobolev t ht s)
    (datumFourierCoeff_reality (u t))
    (datumFourierCoeff_solenoidal (u t) (h.spatial_data t ht).smooth
      (h.spatial_data t ht).periodic (h.spatial_data t ht).divergence_free)
  have heq : smoothFourierSynthesis (referenceSobolevAt h 0 t ht).val = u t :=
    smoothFourierSynthesis_eq_original (u t) (h.spatial_data t ht).smooth
      (h.spatial_data t ht).periodic
  rwa [heq] at hc

/-- Literal Fourier transform of the physical NSE equation before pressure elimination. -/
theorem NSSolution.fourier_equation (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    datumFourierCoeff (timeDerivative u t) k i +
        datumFourierCoeff (convection (u t)) k i +
        datumFourierCoeff (gradient (p t)) k i =
      -((ν * laplaceSymbol k : ℝ) : ℂ) * datumFourierCoeff (u t) k i := by
  have hf : timeDerivative u t + convection (u t) + gradient (p t) =
      ν • laplacian (u t) := funext (h.equation t ht)
  have hc := congrArg datumFourierCoeff hf
  have hdt := h.timeDerivative_spatial_continuous t ht
  have hconv := (convection_contDiff (u t) (h.spatial_data t ht).smooth).continuous
  rw [datumFourierCoeff_add _ _ (hdt.add hconv) (h.pressure_gradient_continuous t ht),
    datumFourierCoeff_add _ _ hdt hconv, datumFourierCoeff_real_smul] at hc
  have hi := congrFun (congrFun hc k) i
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul] at hi
  rw [datumFourierCoeff_laplacian_apply (u t) (h.spatial_data t ht).smooth
    (h.spatial_data t ht).periodic] at hi
  calc
    _ = (ν : ℂ) * (-(laplaceSymbol k : ℂ) * datumFourierCoeff (u t) k i) := hi
    _ = _ := by push_cast; ring

/-- Pressure elimination is derived from actual gradient and solenoidal coefficients. -/
theorem NSSolution.projected_fourier_equation (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    datumFourierCoeff (timeDerivative u t) k i =
      -((ν * laplaceSymbol k : ℝ) : ℂ) * datumFourierCoeff (u t) k i -
        projectedTransportCoefficient k i
          (referenceSobolevAt h 0 t ht) (referenceSobolevAt h 0 t ht) := by
  have hu := datumFourierCoeff_solenoidal (u t) (h.spatial_data t ht).smooth
    (h.spatial_data t ht).periodic (h.spatial_data t ht).divergence_free k
  have hd := h.timeDerivative_fourier_solenoidal t ht k
  have hp := coefficientLeray_datumFourierCoeff_gradient (p t)
    (h.pressure_spatial_smooth t ht) (h.pressure_periodic t ht) k
  have hvec : datumFourierCoeff (timeDerivative u t) k +
      datumFourierCoeff (convection (u t)) k + datumFourierCoeff (gradient (p t)) k =
        fun j => -((ν * laplaceSymbol k : ℝ) : ℂ) * datumFourierCoeff (u t) k j := by
    funext j
    exact h.fourier_equation t ht k j
  have hproj := congrArg (fun v : Fin 3 → ℂ => coefficientLeray k v i) hvec
  rw [coefficientLeray_add_native, coefficientLeray_add_native,
    SingularClosure.coefficientLeray_eq_of_solenoidal k _ hd, hp,
    coefficientLeray_complex_mul_native,
    SingularClosure.coefficientLeray_eq_of_solenoidal k _ hu] at hproj
  simp only [Pi.add_apply, Pi.zero_apply, add_zero] at hproj
  rw [h.convection_fourier_eq t ht] at hproj
  rw [projectedTransportCoefficient_apply]
  change datumFourierCoeff (timeDerivative u t) k i =
    -((ν * laplaceSymbol k : ℝ) : ℂ) * datumFourierCoeff (u t) k i -
      coefficientLeray k (fullTransportCoefficients (referenceSobolevAt h 0 t ht) k) i
  linear_combination hproj

/-- The actual coefficient ODE holds with the native time-zero derivative. -/
theorem NSSolution.coefficient_ode (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun r => datumFourierCoeff (u r) k i)
      (-((ν * laplaceSymbol k : ℝ) : ℂ) * datumFourierCoeff (u t) k i -
        projectedTransportCoefficient k i
          (referenceSobolevAt h 0 t ht) (referenceSobolevAt h 0 t ht)) (Ici 0) t := by
  rw [← h.projected_fourier_equation t ht k i]
  exact h.fourierCoeff_hasDerivWithinAt t ht k i

end
end QuantumAdapter.Obligations
