import NSEMaxwell.DominatedWithin
import NSEMaxwell.Spacetime
import NSEMaxwell.PeriodicIntegration

/-!
# Temporal differentiation of the actual periodic spatial mean

The compact fundamental cube gives a locally uniform bound for the genuine
right time derivative. The dominated within-derivative theorem then commutes
the Bochner integral with differentiation at every nonnegative time, including
the endpoint zero. No time-extension or Fourier premise is used.
-/

set_option autoImplicit false

namespace NSEMaxwell.TemporalMean

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

theorem local_uniform_time_bound
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, IntegrableOn (fun _ : Vec => C) unitCube ∧
      ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, ∀ x ∈ unitCube,
        ‖u s x - u t x‖ ≤ C * ‖s - t‖ := by
  have hcompact : IsCompact (Icc (0 : ℝ) (t + 1) ×ˢ unitCube) :=
    isCompact_Icc.prod isCompact_unitCube
  have hsub : Icc (0 : ℝ) (t + 1) ×ˢ unitCube ⊆ forwardSpacetime := by
    intro z hz
    exact hz.1.1
  have hcont : ContinuousOn (fun z : ℝ × Vec => timeDerivative u z.1 z.2)
      (Icc (0 : ℝ) (t + 1) ×ˢ unitCube) :=
    (timeDerivative_smooth hu).continuousOn.mono hsub
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨C, integrableOn_unitCube_of_continuous continuous_const, ?_⟩
  have hupper : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, s < t + 1 :=
    (Iio_mem_nhds (lt_add_one t)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hupper] with s hs hsu
  intro x hx
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r : ℝ => u r x) (f' := fun r : ℝ => timeDerivative u r x)
    (s := Icc (0 : ℝ) (t + 1)) (C := C)
    (fun r hr => (time_slice_hasDerivWithinAt hu hr.1 x).mono
      (fun q hq => hq.1))
    (fun r hr => hC (r, x) ⟨hr, hx⟩)
    (convex_Icc (0 : ℝ) (t + 1))
    (show t ∈ Icc (0 : ℝ) (t + 1) from ⟨ht, le_add_of_nonneg_right zero_le_one⟩)
    (show s ∈ Icc (0 : ℝ) (t + 1) from ⟨hs, hsu.le⟩)

/-- The spatial mean has the integral of the specified right derivative. -/
theorem mean_time_hasDerivWithinAt
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => spatialMean (u s))
      (spatialMean (timeDerivative u t)) (Ici (0 : ℝ)) t := by
  obtain ⟨C, hCint, hC⟩ := local_uniform_time_bound hu ht
  have hF : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, IntegrableOn (u s) unitCube := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact integrableOn_unitCube_of_continuous (velocity_slice_smooth hu hs).continuous
  have hF0 : IntegrableOn (u t) unitCube :=
    integrableOn_unitCube_of_continuous (velocity_slice_smooth hu ht).continuous
  have hF' : IntegrableOn (timeDerivative u t) unitCube :=
    integrableOn_unitCube_of_continuous
      (velocity_slice_smooth (timeDerivative_smooth hu) ht).continuous
  have hb : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t,
      ∀ᵐ x ∂volume.restrict unitCube, ‖u s x - u t x‖ ≤ C * ‖s - t‖ := by
    filter_upwards [hC] with s hs
    exact (ae_restrict_mem isCompact_unitCube.isClosed.measurableSet).mono
      (fun x hx => hs x hx)
  exact NSEMaxwell.DominatedWithin.hasDerivWithinAt_integral_of_dominated
    hF hF0 hF' hb hCint
    (Filter.Eventually.of_forall (fun x => time_slice_hasDerivWithinAt hu ht x))

theorem mean_time_derivWithin
    {u : Velocity} (hu : SmoothVelocity u) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun s : ℝ => spatialMean (u s)) (Ici (0 : ℝ)) t =
      spatialMean (timeDerivative u t) :=
  (mean_time_hasDerivWithinAt hu ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- A fixed velocity mean gives a mean-zero temporal derivative. -/
theorem timeDerivative_mean_zero_of_constant_mean
    {u : Velocity} (hu : SmoothVelocity u) (m : Vec)
    (hm : ∀ s : ℝ, 0 ≤ s → spatialMean (u s) = m)
    {t : ℝ} (ht : 0 ≤ t) : spatialMean (timeDerivative u t) = 0 := by
  rw [← mean_time_derivWithin hu ht]
  have hc : derivWithin (fun s : ℝ => spatialMean (u s)) (Ici (0 : ℝ)) t =
      derivWithin (fun _ : ℝ => m) (Ici (0 : ℝ)) t := by
    apply derivWithin_congr
    · intro s hs
      exact hm s hs
    · exact hm t ht
  rw [hc]
  simp

end

end NSEMaxwell.TemporalMean
