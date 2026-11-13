import NSEMaxwell.AnalyticContracts

/-!
# The constrained Maxwell existence statement implies Fefferman B

The concrete reconstruction uses the frozen canonical periodic pressure and
retains every PeriodicAnalyticLaws premise. The original proof bodies and
declaration names are preserved.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical NSEMaxwell.Constitutive
open scoped ContDiff

noncomputable section

/-- The momentum split requires no additivity assertion for total Fourier sums. -/
theorem canonical_momentum_split
    (laws : PeriodicAnalyticLaws) (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) (t : ℝ) (ht : 0 ≤ t) :
    momentumResidual ν (canonicalVelocity m B)
        (canonicalPressureTrajectory ν m B) t =
      K (timeDerivative B t) + K (spatialCurl (G ν m (B t))) := by
  have hs := hB.slice ht
  have hG : G ν m (B t) = lambField m (B t) + ν • spatialCurl (B t) := rfl
  have hLamb : convection (U m (B t)) =
      lambField m (B t) + NSEMaxwell.Classical.gradient (kineticPotential m (B t)) :=
    NSEMaxwell.Lamb.reconstructed_lamb_identity m (B t)
      (laws.reconstruction_data m (B t) hs) (laws.reconstruct_curl m (B t) hs)
  have hViscosity : ν • NSEMaxwell.Classical.laplacian (U m (B t)) = -(ν • spatialCurl (B t)) :=
    NSEMaxwell.CurlCurl.reconstructed_viscosity_identity ν m (B t)
      (laws.reconstruction_data m (B t) hs) (laws.reconstruct_curl m (B t) hs)
  have hReg := laws.canonical_regularity ν 0 m B hB
  have hPressure : NSEMaxwell.Classical.gradient (canonicalPressure ν m (B t)) =
      NSEMaxwell.Classical.gradient (headPotential ν m (B t)) - NSEMaxwell.Classical.gradient (kineticPotential m (B t)) :=
    canonicalPressure_gradient ν m (B t)
      (velocity_slice_smooth hReg.velocity_smooth ht)
      (pressure_slice_smooth hReg.pressure_smooth ht)
  change timeDerivative (canonicalVelocity m B) t + convection (U m (B t)) +
      NSEMaxwell.Classical.gradient (canonicalPressure ν m (B t)) - ν • NSEMaxwell.Classical.laplacian (U m (B t)) = _
  rw [laws.reconstruction_time m B hB t ht, hLamb,
    hPressure, hViscosity]
  calc
    K (timeDerivative B t) +
        (lambField m (B t) + NSEMaxwell.Classical.gradient (kineticPotential m (B t))) +
        (NSEMaxwell.Classical.gradient (headPotential ν m (B t)) - NSEMaxwell.Classical.gradient (kineticPotential m (B t))) -
        -(ν • spatialCurl (B t)) =
      K (timeDerivative B t) +
        (G ν m (B t) + NSEMaxwell.Classical.gradient (headPotential ν m (B t))) := by rw [hG]; abel
    _ = K (timeDerivative B t) + K (spatialCurl (G ν m (B t))) := by
      rw [laws.electric_hodge ν m (B t) hs]

/-- Full off-solution factorization retains its own explicit additivity premise.
This premise is unnecessary for, and absent from, the root existence theorem. -/
theorem canonical_momentum_factorization
    (laws : PeriodicAnalyticLaws) (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) (t : ℝ) (ht : 0 ≤ t)
    (hKAdd : K (timeDerivative B t + spatialCurl (G ν m (B t))) =
      K (timeDerivative B t) + K (spatialCurl (G ν m (B t)))) :
    momentumResidual ν (canonicalVelocity m B)
        (canonicalPressureTrajectory ν m B) t =
      K (faradayResidual ν m B t) := by
  rw [canonical_momentum_split laws ν m B hB t ht]
  exact hKAdd.symm

/-- On Faraday solutions, concrete K-negation suffices to cancel momentum. -/
theorem canonical_momentum_zero_of_faraday
    (laws : PeriodicAnalyticLaws) (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) (t : ℝ) (ht : 0 ≤ t)
    (hFaraday : faradayResidual ν m B t = 0) :
    momentumResidual ν (canonicalVelocity m B)
      (canonicalPressureTrajectory ν m B) t = 0 := by
  rw [canonical_momentum_split laws ν m B hB t ht,
    timeDerivative_eq_evolution_of_faraday ν m B t hFaraday,
    V_eq_neg_curl_G, K_neg, neg_add_cancel]

/-- Reverse construction with the explicit canonical periodic pressure. -/
theorem ns_of_maxwell
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity)
    (h : MaxwellSolution ν c m B₀ B E ρ J) :
    NSSolution ν (U m B₀) (canonicalVelocity m B)
      (canonicalPressureTrajectory ν m B) := by
  have hB : MagneticPath B :=
    ⟨h.magnetic_smooth, h.magnetic_periodic, h.magnetic_gauss, h.magnetic_mean_zero⟩
  have hReg := laws.canonical_regularity ν c m B hB
  refine {
    velocity_smooth := hReg.velocity_smooth
    pressure_smooth := hReg.pressure_smooth
    velocity_periodic := hReg.velocity_periodic
    pressure_periodic := hReg.pressure_periodic
    divergence_free := hReg.velocity_divergence_free
    equation := ?_
    initial := ?_ }
  · intro t ht x
    have hR : momentumResidual ν (canonicalVelocity m B)
        (canonicalPressureTrajectory ν m B) t = 0 := by
      exact canonical_momentum_zero_of_faraday laws ν m B hB t ht
        (canonical_faraday_of_maxwell ν c m B₀ B E ρ J h t ht)
    exact sub_eq_zero.mp (congrFun hR x)
  · change U m (B 0) = U m B₀
    rw [h.initial]

/-- Reverse existence transport with the exact reconstructed datum and pressure. -/
theorem maxwellB_implies_feffermanB_of_periodicAnalyticLaws
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) :
    MaxwellB ν c → FeffermanB ν := by
  intro hMB a ha
  obtain ⟨B, E, ρ, J, h⟩ :=
    hMB (spatialMean a) (spatialCurl a) (laws.curl_data a ha)
  have hNS := ns_of_maxwell laws ν c (spatialMean a) (spatialCurl a) B E ρ J h
  rw [laws.reconstruct_velocity a ha] at hNS
  exact ⟨canonicalVelocity (spatialMean a) B,
    canonicalPressureTrajectory ν (spatialMean a) B, hNS⟩

end

end NSEMaxwell.Bridge
