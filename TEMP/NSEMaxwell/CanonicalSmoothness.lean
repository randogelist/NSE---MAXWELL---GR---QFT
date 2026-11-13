import NSEMaxwell.AnalyticBridge
import NSEMaxwell.LocalEvolution
import NSEMaxwell.FourierPeriodic

/-!
# Reduction of canonical smoothness to the canonical potentials

Smoothness of the induced electric field, charge, and current follows from
smoothness of reconstructed velocity on every magnetic path. In particular the
evolution direction V = -curl G is itself a magnetic path, so the same velocity
smoothing endpoint supplies smoothness of K V. The remaining pressure and
velocity-divergence assertions are not assumed or discharged by this module.
-/

set_option autoImplicit false

namespace NSEMaxwell.CanonicalSmoothness

open NSEMaxwell.Classical NSEMaxwell.Bridge NSEMaxwell.Spacetime
open NSEMaxwell.LocalEvolution NSEMaxwell.PeriodicIntegration NSEMaxwell.FourierPeriodic
open MeasureTheory
open scoped ContDiff BigOperators

noncomputable section

theorem divergence_trajectory_smooth
    {u : Velocity} (hu : SmoothVelocity u) :
    SmoothPressure (fun t => NSEMaxwell.Classical.divergence (u t)) := by
  have hc (i : Fin 3) :=
    (contDiffOn_piLp 2).mp (coordinateDerivative_trajectory_smooth hu i) i
  simpa [SmoothPressure, NSEMaxwell.Classical.divergence,
    Fin.sum_univ_succ, add_assoc] using
    ((hc 0).add (hc 1)).add (hc 2)

theorem canonical_electric_smooth
    (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : SmoothVelocity B) (hU : SmoothVelocity (canonicalVelocity m B)) :
    SmoothVelocity (canonicalElectric ν m B) := by
  exact (cross_trajectory_smooth hB hU).add
    ((curl_trajectory_smooth hB).const_smul ν)

theorem canonical_charge_smooth
    (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : SmoothVelocity B) (hU : SmoothVelocity (canonicalVelocity m B)) :
    SmoothPressure (canonicalCharge ν m B) :=
  divergence_trajectory_smooth (canonical_electric_smooth ν m B hB hU)

/-- Every smooth periodic curl trajectory is an admissible magnetic path. -/
theorem magnetic_curl_path
    (u : Velocity) (hu : SmoothVelocity u) (hp : PeriodicVelocity u) :
    MagneticPath (fun t => spatialCurl (u t)) := by
  refine ⟨curl_trajectory_smooth hu, ?_, ?_, ?_⟩
  · intro t ht
    exact spatialCurl_periodic (hp t ht)
  · intro t ht x
    exact congrFun (NSEMaxwell.CurlCurl.divergence_curl
      (velocity_slice_smooth hu ht)) x
  · intro t ht
    exact spatialMean_curl_zero (velocity_slice_smooth hu ht) (hp t ht)

theorem magnetic_neg_path
    (B : Velocity) (hB : MagneticPath B) :
    MagneticPath (fun t x => -B t x) := by
  refine ⟨hB.smooth.neg, ?_, ?_, ?_⟩
  · intro t ht x i
    change -(B t (x + unitVector i)) = -(B t x)
    rw [hB.periodic t ht x i]
  · intro t ht x
    change NSEMaxwell.Classical.divergence (-(B t)) x = 0
    calc
      NSEMaxwell.Classical.divergence (-(B t)) x =
          -NSEMaxwell.Classical.divergence (B t) x := by
        simp [NSEMaxwell.Classical.divergence, coordinateDerivative_neg,
          Finset.sum_neg_distrib]
      _ = 0 := by rw [hB.divergence_free t ht x, neg_zero]
  · intro t ht
    change (∫ x in unitCube, -(B t x)) = 0
    rw [integral_neg]
    change -spatialMean (B t) = 0
    rw [hB.mean_zero t ht, neg_zero]

/-- The constitutive evolution direction is magnetic without an evolution equation. -/
theorem evolution_magnetic_path
    (ν : ℝ) (m : Vec) (B : Velocity) (hB : MagneticPath B)
    (hU : SmoothVelocity (canonicalVelocity m B)) :
    MagneticPath (fun t => V ν m (B t)) := by
  exact magnetic_neg_path _
    (magnetic_curl_path (canonicalElectric ν m B)
      (canonical_electric_smooth ν m B hB.smooth hU)
      (canonicalElectric_periodic ν m hB.periodic))

/-- Current smoothness uses the same velocity-smoothing premise on V. -/
theorem canonical_current_smooth_of_velocity_smoothing
    (hU : ∀ (m : Vec) (B : Velocity), MagneticPath B →
      SmoothVelocity (canonicalVelocity m B))
    (ν c : ℝ) (m : Vec) (B : Velocity) (hB : MagneticPath B) :
    SmoothVelocity (canonicalCurrent ν c m B) := by
  have hu := hU m B hB
  have hv := evolution_magnetic_path ν m B hB hu
  have hkv : SmoothVelocity (fun t x => K (V ν m (B t)) x) := by
    simpa only [SmoothVelocity, canonicalVelocity, U, zero_add] using
      hU 0 (fun t => V ν m (B t)) hv
  have hdg : SmoothVelocity (fun t => DG ν m (B t) (V ν m (B t))) := by
    exact ((cross_trajectory_smooth hv.smooth hu).add
      (cross_trajectory_smooth hB.smooth hkv)).add
      ((curl_trajectory_smooth hv.smooth).const_smul ν)
  exact ((curl_trajectory_smooth hB.smooth).const_smul (c ^ 2)).sub hdg

end

end NSEMaxwell.CanonicalSmoothness
