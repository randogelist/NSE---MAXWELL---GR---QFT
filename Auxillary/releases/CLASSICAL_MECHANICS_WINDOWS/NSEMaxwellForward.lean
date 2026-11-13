import NSEMaxwell.AnalyticContracts

/-!
# Fefferman B implies the constrained Maxwell existence statement

The concrete construction retains the arbitrary velocity mean and every
PeriodicAnalyticLaws premise. The original proof bodies and declaration names
are preserved. No global-existence assertion is introduced.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical NSEMaxwell.Constitutive
open scoped ContDiff

noncomputable section

theorem momentum_zero_of_ns {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolution ν a u p) (t : ℝ) (ht : 0 ≤ t) :
    momentumResidual ν u p t = 0 := by
  funext x
  exact sub_eq_zero.mpr (h.equation t ht x)

/-- Canonical Maxwell fields are an exact solution once Faraday vanishes. -/
theorem maxwell_of_faraday
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B : Velocity) (hB : MagneticPath B) (hInitial : B 0 = B₀)
    (hFaraday : ∀ t : ℝ, 0 ≤ t → faradayResidual ν m B t = 0) :
    MaxwellSolution ν c m B₀ B (canonicalElectric ν m B)
      (canonicalCharge ν m B) (canonicalCurrent ν c m B) := by
  have hReg := laws.canonical_regularity ν c m B hB
  refine {
    magnetic_smooth := hB.smooth
    electric_smooth := hReg.electric_smooth
    charge_smooth := hReg.charge_smooth
    current_smooth := hReg.current_smooth
    magnetic_periodic := hB.periodic
    electric_periodic := hReg.electric_periodic
    charge_periodic := hReg.charge_periodic
    current_periodic := hReg.current_periodic
    magnetic_mean_zero := hB.mean_zero
    magnetic_gauss := hB.divergence_free
    faraday := ?_
    electric_gauss := ?_
    ampere := ?_
    constitutive_electric := ?_
    constitutive_charge := ?_
    constitutive_current := ?_
    initial := hInitial }
  · intro t ht x
    exact congrFun (hFaraday t ht) x
  · intro t ht x
    rfl
  · intro t ht x
    apply canonical_ampere_of_residual_zero ν c m B t
    exact ampere_zero_of_faraday_chain ν c m B t
      (laws.electric_time_chain ν m B hB t ht)
      (hFaraday t ht)
  · intro t ht
    rfl
  · intro t ht
    rfl
  · intro t ht
    rfl

/-- The actual velocity mean is retained in the vorticity reconstruction. -/
theorem faraday_of_ns
    (laws : PeriodicAnalyticLaws) (ν : ℝ) (m : Vec) (a : Field)
    (u : Velocity) (p : Pressure) (h : NSSolution ν a u p)
    (hMean : spatialMean a = m) (t : ℝ) (ht : 0 ≤ t) :
    faradayResidual ν m (curlTrajectory u) t = 0 := by
  have hMeanT : spatialMean (u t) = m := by
    calc
      spatialMean (u t) = spatialMean (u 0) :=
        laws.mean_conservation ν u p h.velocity_smooth h.pressure_smooth
          h.velocity_periodic h.pressure_periodic h.divergence_free
          (momentum_zero_of_ns h) t ht
      _ = spatialMean a := congrArg spatialMean h.initial
      _ = m := hMean
  have hRecon : U m (spatialCurl (u t)) = u t := by
    simpa only [hMeanT] using laws.reconstruct_velocity (u t) (h.slice_data ht)
  have hG : G ν m (spatialCurl (u t)) =
      (fun x => cross (spatialCurl (u t) x) (u t x) +
        ν • spatialCurl (spatialCurl (u t)) x) := by
    unfold G
    rw [hRecon]
  have hCurlR : spatialCurl (momentumResidual ν u p t) =
      faradayResidual ν m (curlTrajectory u) t := by
    rw [laws.vorticity_residual ν u p h.velocity_smooth h.pressure_smooth
      h.velocity_periodic h.pressure_periodic h.divergence_free t ht]
    change timeDerivative (curlTrajectory u) t +
        spatialCurl (fun x => cross (spatialCurl (u t) x) (u t x) +
          ν • spatialCurl (spatialCurl (u t)) x) =
      timeDerivative (curlTrajectory u) t + spatialCurl (G ν m (spatialCurl (u t)))
    rw [hG]
  rw [momentum_zero_of_ns h t ht, spatialCurl_zero] at hCurlR
  exact hCurlR.symm

/-- Forward construction on actual fields and on the prescribed initial datum. -/
theorem maxwell_of_ns
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) (m : Vec) (B₀ : Field)
    (hB₀ : MagneticData B₀) (u : Velocity) (p : Pressure)
    (h : NSSolution ν (U m B₀) u p) :
    MaxwellSolution ν c m B₀ (curlTrajectory u)
      (canonicalElectric ν m (curlTrajectory u))
      (canonicalCharge ν m (curlTrajectory u))
      (canonicalCurrent ν c m (curlTrajectory u)) := by
  apply maxwell_of_faraday laws ν c m B₀ (curlTrajectory u)
  · exact laws.vorticity_regularity u h.velocity_smooth h.velocity_periodic
      h.divergence_free
  · change spatialCurl (u 0) = B₀
    rw [h.initial, laws.reconstruct_curl m B₀ hB₀]
  · exact faraday_of_ns laws ν m (U m B₀) u p h
      (laws.reconstruct_mean m B₀ hB₀)

/-- Forward existence transport with all concrete analytic premises explicit. -/
theorem feffermanB_implies_maxwellB_of_periodicAnalyticLaws
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) :
    FeffermanB ν → MaxwellB ν c := by
  intro hFB m B₀ hB₀
  obtain ⟨u, p, h⟩ := hFB (U m B₀) (laws.reconstruction_data m B₀ hB₀)
  exact ⟨curlTrajectory u, canonicalElectric ν m (curlTrajectory u),
    canonicalCharge ν m (curlTrajectory u), canonicalCurrent ν c m (curlTrajectory u),
    maxwell_of_ns laws ν c m B₀ hB₀ u p h⟩

end

end NSEMaxwell.Bridge
