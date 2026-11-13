import FourierHodgeLaws.ParameterCoefficients

/-!
Isolated proof-body endpoint: ME12
Upstream: NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt
Source: https://github.com/randogelist/Methlib/blob/eac159c5f7bf5a99a00d994da34c4760ea8335d0/FourierHodgeLaws_inhabitant/FourierHodgeLaws/ParameterCoefficients.lean#L81
Source SHA256: 016d9cf0c1deda75770d39f66c2e5c684435448bc7c9785cbc5d28612db54eee
Original source lines: 81-102
Status: A_TIER_CANDIDATE. No local Lean execution.
Dependencies remain explicitly imported; this is not a dependency-free theorem.
The proof body is copied; only the exported declaration name is changed.
-/

set_option autoImplicit false
set_option Elab.async true


namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration
open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem _root_.GRTemp.ME12.endpoint (F : ℝ → Vec → E)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) forwardSpacetime)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => ∫ x in unitCube, F s x)
      (∫ x in unitCube, cubeTimeDerivative F t x) (Ici (0 : ℝ)) t := by
  obtain ⟨C, hCint, hC⟩ := cubeIntegral_local_uniform_time_bound F hF ht
  have hFi : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, IntegrableOn (F s) unitCube := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact integrableOn_unitCube_of_continuous (cubeSlice_contDiff F hF hs).continuous
  have hF0 : IntegrableOn (F t) unitCube :=
    integrableOn_unitCube_of_continuous (cubeSlice_contDiff F hF ht).continuous
  have hFd : IntegrableOn (cubeTimeDerivative F t) unitCube :=
    integrableOn_unitCube_of_continuous
      (cubeSlice_contDiff _ (cubeTimeDerivative_smooth F hF) ht).continuous
  have hb : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t,
      ∀ᵐ x ∂volume.restrict unitCube, ‖F s x - F t x‖ ≤ C * ‖s - t‖ := by
    filter_upwards [hC] with s hs
    exact (ae_restrict_mem isCompact_unitCube.isClosed.measurableSet).mono
      (fun x hx => hs x hx)
  exact NSEMaxwell.DominatedWithin.hasDerivWithinAt_integral_of_dominated
    hFi hF0 hFd hb hCint
    (Filter.Eventually.of_forall (fun x => cubeTime_hasDerivWithinAt F hF ht x))

end

end NSEMaxwell.HodgeProof
