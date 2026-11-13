import QuantumAdapter.Transport

/-!
Native L2 norm identities for the actual complex wave representative.
The real L2 inner product is used only to express the squared Hilbert norm
as the integral of the complex Born density. Conditional transport preserves
this norm under the existing two analytic transport laws; no new law or
selfadjoint generator is introduced.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory

namespace QuantumAdapter

noncomputable section

theorem memLp_bornDensity_integrable {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : MemLp ψ 2 μ) :
    Integrable (bornDensity ψ) μ := by
  have hi := (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ
  change Integrable (fun q => Complex.normSq (ψ q)) μ
  simpa only [Complex.normSq_eq_norm_sq] using hi

theorem memLp_toLp_norm_sq {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : MemLp ψ 2 μ) :
    ‖hψ.toLp ψ‖ ^ 2 = ∫ q, bornDensity ψ q ∂μ := by
  rw [← real_inner_self_eq_norm_sq (hψ.toLp ψ), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψ.coeFn_toLp] with q hq
  rw [real_inner_self_eq_norm_sq, hq]
  exact (Complex.normSq_eq_norm_sq (ψ q)).symm

theorem WaveAdmissible.norm_toL2 {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ) :
    ‖hψ.toL2‖ = 1 := by
  have hs : ‖hψ.toL2‖ ^ 2 = 1 :=
    (memLp_toLp_norm_sq hψ.memLp).trans hψ.normalized
  nlinarith [norm_nonneg hψ.toL2]

theorem halfDensityPullback_toLp_norm {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {κ : ℝ} {Φ : ℝ → E → E}
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    {ψ : Wave E} (hψ : MemLp ψ 2 μ) (t : ℝ) :
    ‖(hLp t ψ hψ).toLp (halfDensityPullback κ Φ t ψ)‖ = ‖hψ.toLp ψ‖ := by
  have hs :
      ‖(hLp t ψ hψ).toLp (halfDensityPullback κ Φ t ψ)‖ ^ 2 =
        ‖hψ.toLp ψ‖ ^ 2 := by
    rw [memLp_toLp_norm_sq, memLp_toLp_norm_sq]
    calc
      (∫ q, bornDensity (halfDensityPullback κ Φ t ψ) q ∂μ) =
          ∫ q, Real.exp (κ * t) * bornDensity ψ (Φ (-t) q) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with q
        exact bornDensity_halfDensityPullback κ Φ t ψ q
      _ = ∫ q, bornDensity ψ q ∂μ :=
        hI t (bornDensity ψ) (memLp_bornDensity_integrable hψ)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end

end QuantumAdapter
