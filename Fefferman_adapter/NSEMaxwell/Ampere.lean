import NSEMaxwell.Constitutive

/-!
# Ampere on Faraday solutions

The existence equivalence requires the constitutive time-chain rule, but does
not require a separate DG-additivity or DG-negation theorem. Faraday identifies
the time derivative directly with the prescribed spatial evolution vector.
-/

set_option autoImplicit false

namespace NSEMaxwell.Constitutive

open NSEMaxwell.Classical

noncomputable section

theorem timeDerivative_eq_evolution_of_faraday
    (ν : ℝ) (m : Vec) (B : Velocity) (t : ℝ)
    (hFaraday : faradayResidual ν m B t = 0) :
    timeDerivative B t = V ν m (B t) := by
  have hR : timeDerivative B t + spatialCurl (G ν m (B t)) = 0 := hFaraday
  change timeDerivative B t = -spatialCurl (G ν m (B t))
  calc
    timeDerivative B t =
      (timeDerivative B t + spatialCurl (G ν m (B t))) -
        spatialCurl (G ν m (B t)) := by abel
    _ = -spatialCurl (G ν m (B t)) := by rw [hR]; simp

/-- Chain rule and Faraday alone imply the exact induced-current Ampere law. -/
theorem ampere_zero_of_faraday_chain
    (ν c : ℝ) (m : Vec) (B : Velocity) (t : ℝ)
    (hChain : timeDerivative (canonicalElectric ν m B) t =
      DG ν m (B t) (timeDerivative B t))
    (hFaraday : faradayResidual ν m B t = 0) :
    ampereResidual ν c m B t = 0 := by
  have hEvolution := timeDerivative_eq_evolution_of_faraday ν m B t hFaraday
  rw [hEvolution] at hChain
  funext x
  change timeDerivative (canonicalElectric ν m B) t x -
      c ^ 2 • spatialCurl (B t) x +
      (c ^ 2 • spatialCurl (B t) x - DG ν m (B t) (V ν m (B t)) x) = 0
  rw [hChain]
  abel

end

end NSEMaxwell.Constitutive
