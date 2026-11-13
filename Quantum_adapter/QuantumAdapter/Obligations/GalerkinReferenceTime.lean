import QuantumAdapter.Obligations.GalerkinReference
import QuantumAdapter.Obligations.GalerkinIntegral
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Native reference Fourier coefficients differentiated at every forward time

Joint smoothness on the closed forward half-space supplies continuous one-sided
time derivatives. Compact spatial-time bounds justify differentiation through
the literal unit-cube Fourier integral, including the initial time.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly NSEMaxwell.Classical

noncomputable section

private theorem uniqueDiffOn_forwardSpacetime_time : UniqueDiffOn ℝ forwardSpacetime := by
  have heq : forwardSpacetime = (Ici (0 : ℝ)) ×ˢ (univ : Set Vec) := by
    ext z
    simp [forwardSpacetime]
  rw [heq]
  exact (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- The derivative furnished by joint smoothness uses the native one-sided convention. -/
theorem NSSolution.time_hasDerivWithinAt (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun r => u r x) (timeDerivative u t x) (Ici 0) t := by
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => u r x) (Ici 0) := by
    simpa only [Function.comp_def] using h.velocity_smooth.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => hr)
  exact (hc.differentiableOn (by simp) t ht).hasDerivWithinAt

/-- Exact identification with the joint derivative in the time coordinate. -/
theorem NSSolution.timeDerivative_eq_joint (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    timeDerivative u t x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime (t, x) (1, 0) := by
  have hc : HasDerivWithinAt (fun r : ℝ => (r, x)) (1, 0) (Ici 0) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hd := ((h.velocity_smooth.differentiableOn (by simp)) (t, x) ht).hasFDerivWithinAt
  have he := hd.comp_hasDerivWithinAt t hc (fun r hr => hr)
  exact he.derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- The actual one-sided time derivative is jointly smooth on the closed half-space. -/
theorem NSSolution.timeDerivative_smooth (h : NSSolution ν a u p) :
    SmoothVelocity (timeDerivative u) := by
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      fderivWithin ℝ (fun y : ℝ × Vec => u y.1 y.2) forwardSpacetime z (1, 0))
      forwardSpacetime :=
    (h.velocity_smooth.fderivWithin uniqueDiffOn_forwardSpacetime_time
      (by simp)).clm_apply contDiffOn_const
  apply hc.congr
  intro z hz
  exact h.timeDerivative_eq_joint z.1 hz z.2

/-- Each time derivative slice is a continuous actual spatial field. -/
theorem NSSolution.timeDerivative_spatial_continuous (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) : Continuous (timeDerivative u t) := by
  have hc : ContDiff ℝ ∞ (timeDerivative u t) := by
    simpa only [Function.comp_def] using h.timeDerivative_smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun x => ht)
  exact hc.continuous

/-- Compactness gives a literal uniform bound on the native time derivative. -/
theorem NSSolution.timeDerivative_uniform_bound (h : NSSolution ν a u p) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ unitCube,
      ‖timeDerivative u t x‖ ≤ B := by
  have hc : ContinuousOn (fun z : ℝ × Vec => timeDerivative u z.1 z.2)
      ((Icc (0 : ℝ) T) ×ˢ unitCube) :=
    h.timeDerivative_smooth.continuousOn.mono (fun z hz => hz.1.1)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_unitCube).exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  exact (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

/-- Differentiation of the literal Fourier integrand, retaining the initial boundary. -/
theorem NSSolution.fourierIntegrand_hasDerivWithinAt (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) (x : Vec) :
    HasDerivWithinAt (fun r => datumFourierIntegrand (u r) k i x)
      (datumFourierIntegrand (timeDerivative u t) k i x) (Ici 0) t := by
  have hr := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    (h.time_hasDerivWithinAt t ht x)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t hr
  simpa only [datumFourierIntegrand, Function.comp_def, EuclideanSpace.coe_proj,
    Complex.ofRealCLM_apply] using hc.const_mul (star (fourierCharacter k x))

/-- The actual Fourier coefficient differentiates under the integral on a finite time interval. -/
theorem NSSolution.fourierCoeff_hasDerivWithinAt_Icc (h : NSSolution ν a u p)
    (T t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) (Icc 0 T) t := by
  obtain ⟨B, hB, hbound⟩ := h.timeDerivative_uniform_bound T
  letI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using isCompact_unitCube.measure_lt_top⟩
  apply hasDerivWithinAt_integral_of_dominated_lip ht
    (fun r hr => datumFourierIntegrand_integrableOn (h.spatial_data r hr.1).smooth.continuous k i)
    (datumFourierIntegrand_integrableOn (h.timeDerivative_spatial_continuous t ht.1) k i)
    (fun _ => B) (integrable_const B) (fun _ => hB)
  · filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    intro r hr
    apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun s => datumFourierIntegrand (timeDerivative u s) k i x)
      (s := Icc (0 : ℝ) T)
    · intro s hs
      exact (h.fourierIntegrand_hasDerivWithinAt s hs.1 k i x).mono Icc_subset_Ici_self
    · intro s hs
      calc
        ‖datumFourierIntegrand (timeDerivative u s) k i x‖ =
            ‖timeDerivative u s x i‖ := by
          simp only [datumFourierIntegrand, norm_mul, norm_star, fourierCharacter_norm,
            one_mul, Complex.norm_real]
        _ ≤ ‖timeDerivative u s x‖ := PiLp.norm_apply_le _ _
        _ ≤ B := hbound s hs x hx
    · exact convex_Icc 0 T
    · exact ht
    · exact hr
  · exact Filter.Eventually.of_forall (fun x =>
      (h.fourierIntegrand_hasDerivWithinAt t ht.1 k i x).mono Icc_subset_Ici_self)

/-- Native coefficient differentiation on the entire forward half-line, including t=0. -/
theorem NSSolution.fourierCoeff_hasDerivWithinAt (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) (Ici 0) t := by
  apply (h.fourierCoeff_hasDerivWithinAt_Icc (t + 1) t
    ⟨ht, by linarith⟩ k i).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < t + 1 by linarith))] with r hr hrt
  exact ⟨hr, hrt.le⟩

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
