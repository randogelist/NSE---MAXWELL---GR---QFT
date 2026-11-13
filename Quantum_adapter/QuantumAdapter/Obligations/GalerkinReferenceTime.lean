import QuantumAdapter.Obligations.GalerkinReference
import QuantumAdapter.Obligations.GalerkinSmoothTime

/-! Native NSSolution specializations of closed-halfspace Fourier differentiation. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
namespace QuantumAdapter.Obligations
open SingularClosure QuantumAdapter.Assembly NSEMaxwell.Classical
noncomputable section
variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

theorem NSSolution.time_hasDerivWithinAt (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun r => u r x) (timeDerivative u t x) (Ici 0) t :=
  h.velocity_smooth.time_hasDerivWithinAt t ht x

theorem NSSolution.timeDerivative_eq_joint (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    timeDerivative u t x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime (t, x) (1, 0) :=
  h.velocity_smooth.timeDerivative_eq_joint t ht x

theorem NSSolution.timeDerivative_smooth (h : NSSolution ν a u p) :
    SmoothVelocity (timeDerivative u) :=
  h.velocity_smooth.timeDerivative_smooth

theorem NSSolution.timeDerivative_spatial_continuous (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) : Continuous (timeDerivative u t) :=
  h.velocity_smooth.timeDerivative_spatial_continuous t ht

theorem NSSolution.timeDerivative_uniform_bound (h : NSSolution ν a u p) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ unitCube,
      ‖timeDerivative u t x‖ ≤ B :=
  h.velocity_smooth.timeDerivative_uniform_bound T

theorem NSSolution.fourierIntegrand_hasDerivWithinAt (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) (x : Vec) :
    HasDerivWithinAt (fun r => datumFourierIntegrand (u r) k i x)
      (datumFourierIntegrand (timeDerivative u t) k i x) (Ici 0) t :=
  h.velocity_smooth.fourierIntegrand_hasDerivWithinAt t ht k i x

theorem NSSolution.fourierCoeff_hasDerivWithinAt_Icc (h : NSSolution ν a u p)
    (T t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) (Icc 0 T) t :=
  h.velocity_smooth.fourierCoeff_hasDerivWithinAt_Icc T t ht k i

theorem NSSolution.fourierCoeff_hasDerivWithinAt (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) (Ici 0) t :=
  h.velocity_smooth.fourierCoeff_hasDerivWithinAt t ht k i

/-- Differentiating the actual divergence constraint gives solenoidality of the time derivative. -/
theorem NSSolution.timeDerivative_fourier_solenoidal (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) :
    SpectralSolenoidal (datumFourierCoeff (timeDerivative u t)) := by
  intro k
  have hd : HasDerivWithinAt
      (fun r => ∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff (u r) k i)
      (∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff (timeDerivative u t) k i)
      (Ici 0) t := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    exact (h.fourierCoeff_hasDerivWithinAt t ht k i).const_mul (k i : ℂ)
  have hz (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :
      (∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff (u r) k i) = 0 :=
    datumFourierCoeff_solenoidal (u r) (h.spatial_data r hr).smooth
      (h.spatial_data r hr).periodic (h.spatial_data r hr).divergence_free k
  have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℂ))
      (∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff (timeDerivative u t) k i)
      (Ici 0) t :=
    hd.congr_of_mem (fun r hr => (hz r hr).symm) ht
  simpa only [derivWithin_const] using
    (hconst.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm

end
end QuantumAdapter.Obligations
