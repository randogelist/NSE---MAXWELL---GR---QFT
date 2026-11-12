import NSEMaxwell.Negation
import NSEMaxwell.Lamb
import NSEMaxwell.Pressure
import NSEMaxwell.Ampere
import NSEMaxwell.ConstantPaths
import NSEMaxwell.CurlCurl

/-!
# Concrete analytic endpoints and the deterministic existence implication

Every field and operator below is the concrete object defined in Classical.lean.
`PeriodicAnalyticLaws` lists unresolved local analytic identities. It contains
neither FeffermanB, MaxwellB, ExactEquivalence, nor a solution-existence map.

The proof terms establish the exact implication from those named identities to
the requested concrete equivalence. No inhabitant of PeriodicAnalyticLaws is
provided. Consequently this module does not prove the unconditional target.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical NSEMaxwell.Constitutive
open scoped ContDiff

noncomputable section

/-- Smooth NSEMaxwell.Classical.divergence-free mean-zero magnetic trajectories, including t = 0. -/
structure MagneticPath (B : Velocity) : Prop where
  smooth : SmoothVelocity B
  periodic : PeriodicVelocity B
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (B t) x = 0
  mean_zero : ∀ t : ℝ, 0 ≤ t → spatialMean (B t) = 0

theorem MagneticPath.slice {B : Velocity} (h : MagneticPath B)
    {t : ℝ} (ht : 0 ≤ t) : MagneticData (B t) := by
  exact ⟨⟨velocity_slice_smooth h.smooth ht, h.periodic t ht,
    h.divergence_free t ht⟩, h.mean_zero t ht⟩

theorem MagneticPath.constant (B : Field) (hB : MagneticData B) :
    MagneticPath (fun _ : ℝ => B) := by
  exact ⟨smooth_constant_velocity B hB.smooth,
    periodic_constant_velocity B hB.periodic,
    fun _ _ => hB.divergence_free, fun _ _ => hB.mean_zero⟩

def curlTrajectory (u : Velocity) : Velocity := fun t => spatialCurl (u t)

def momentumResidual (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) : Field :=
  timeDerivative u t + convection (u t) + NSEMaxwell.Classical.gradient (p t) - ν • NSEMaxwell.Classical.laplacian (u t)

def lambField (m : Vec) (B : Field) : Field :=
  fun x => cross (B x) (U m B x)

def kineticPotential (m : Vec) (B : Field) : ScalarField :=
  fun x => ‖U m B x‖ ^ 2 / 2

def headPotential (ν : ℝ) (m : Vec) (B : Field) : ScalarField :=
  scalarL (Q ν m B)

/-- Regularity of explicitly constructed fields; no evolution is assumed. -/
structure CanonicalRegularity (ν c : ℝ) (m : Vec) (B : Velocity) : Prop where
  velocity_smooth : SmoothVelocity (canonicalVelocity m B)
  pressure_smooth : SmoothPressure (canonicalPressureTrajectory ν m B)
  electric_smooth : SmoothVelocity (canonicalElectric ν m B)
  charge_smooth : SmoothPressure (canonicalCharge ν m B)
  current_smooth : SmoothVelocity (canonicalCurrent ν c m B)
  velocity_periodic : PeriodicVelocity (canonicalVelocity m B)
  pressure_periodic : PeriodicPressure (canonicalPressureTrajectory ν m B)
  electric_periodic : PeriodicVelocity (canonicalElectric ν m B)
  charge_periodic : PeriodicPressure (canonicalCharge ν m B)
  current_periodic : PeriodicVelocity (canonicalCurrent ν c m B)
  velocity_divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    NSEMaxwell.Classical.divergence (canonicalVelocity m B t) x = 0

/--
OPEN ANALYTIC PREMISES. Each field is a concrete analytic statement, not a new
axiom declaration. An unconditional root theorem requires a proved inhabitant
of this structure. No such inhabitant is asserted in this repository.
-/
structure PeriodicAnalyticLaws : Prop where
  reconstruct_velocity : ∀ (a : Field), Data a →
    U (spatialMean a) (spatialCurl a) = a
  reconstruct_curl : ∀ (m : Vec) (B : Field), MagneticData B →
    spatialCurl (U m B) = B
  vorticity_regularity : ∀ (u : Velocity),
    SmoothVelocity u → PeriodicVelocity u →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0) →
    MagneticPath (curlTrajectory u)
  canonical_regularity : ∀ (ν c : ℝ) (m : Vec) (B : Velocity),
    MagneticPath B → CanonicalRegularity ν c m B
  mean_conservation : ∀ (ν : ℝ) (u : Velocity) (p : Pressure),
    SmoothVelocity u → SmoothPressure p →
    PeriodicVelocity u → PeriodicPressure p →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0) →
    (∀ t : ℝ, 0 ≤ t → momentumResidual ν u p t = 0) →
    ∀ t : ℝ, 0 ≤ t → spatialMean (u t) = spatialMean (u 0)
  vorticity_residual : ∀ (ν : ℝ) (u : Velocity) (p : Pressure),
    SmoothVelocity u → SmoothPressure p →
    PeriodicVelocity u → PeriodicPressure p →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, NSEMaxwell.Classical.divergence (u t) x = 0) →
    ∀ t : ℝ, 0 ≤ t →
    spatialCurl (momentumResidual ν u p t) =
      timeDerivative (curlTrajectory u) t +
        spatialCurl (fun x => cross (spatialCurl (u t) x) (u t x) +
          ν • spatialCurl (spatialCurl (u t)) x)
  reconstruction_time : ∀ (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    timeDerivative (canonicalVelocity m B) t = K (timeDerivative B t)
  electric_hodge : ∀ (ν : ℝ) (m : Vec) (B : Field), MagneticData B →
    G ν m B + NSEMaxwell.Classical.gradient (headPotential ν m B) = K (spatialCurl (G ν m B))
  electric_time_chain : ∀ (ν : ℝ) (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    timeDerivative (canonicalElectric ν m B) t =
      DG ν m (B t) (timeDerivative B t)

/-- Initial vorticity admissibility follows by applying path regularity to a
constant trajectory. It is not an independent analytic premise. -/
theorem PeriodicAnalyticLaws.curl_data
    (laws : PeriodicAnalyticLaws) (a : Field) (ha : Data a) :
    MagneticData (spatialCurl a) := by
  have h := laws.vorticity_regularity (fun _ : ℝ => a)
    (smooth_constant_velocity a ha.smooth)
    (periodic_constant_velocity a ha.periodic)
    (fun _ _ => ha.divergence_free)
  exact h.slice (t := 0) (le_refl 0)

/-- Admissibility of reconstructed initial velocity is a constant-path slice
of the already required canonical regularity endpoint. -/
theorem PeriodicAnalyticLaws.reconstruction_data
    (laws : PeriodicAnalyticLaws) (m : Vec) (B : Field) (hB : MagneticData B) :
    Data (U m B) := by
  have h := laws.canonical_regularity 0 0 m (fun _ : ℝ => B)
    (MagneticPath.constant B hB)
  exact ⟨velocity_slice_smooth h.velocity_smooth (t := 0) (le_refl 0),
    h.velocity_periodic 0 (le_refl 0), h.velocity_divergence_free 0 (le_refl 0)⟩

/-- Mean reconstruction follows from the two Hodge inverse identities by
pointwise cancellation; it is not an additional integral premise. -/
theorem PeriodicAnalyticLaws.reconstruct_mean
    (laws : PeriodicAnalyticLaws) (m : Vec) (B : Field) (hB : MagneticData B) :
    spatialMean (U m B) = m := by
  have h := laws.reconstruct_velocity (U m B) (laws.reconstruction_data m B hB)
  rw [laws.reconstruct_curl m B hB] at h
  have hx := congrFun h (0 : Vec)
  change spatialMean (U m B) + K B 0 = m + K B 0 at hx
  exact add_right_cancel hx

theorem momentum_zero_of_ns {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolution ν a u p) (t : ℝ) (ht : 0 ≤ t) :
    momentumResidual ν u p t = 0 := by
  funext x
  exact sub_eq_zero.mpr (h.equation t ht x)

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

/-- Conditional equivalence of the exact concrete global existence statements. -/
theorem feffermanB_iff_maxwellB_of_periodicAnalyticLaws
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) :
    FeffermanB ν ↔ MaxwellB ν c := by
  constructor
  · intro hFB m B₀ hB₀
    obtain ⟨u, p, h⟩ := hFB (U m B₀) (laws.reconstruction_data m B₀ hB₀)
    exact ⟨curlTrajectory u, canonicalElectric ν m (curlTrajectory u),
      canonicalCharge ν m (curlTrajectory u), canonicalCurrent ν c m (curlTrajectory u),
      maxwell_of_ns laws ν c m B₀ hB₀ u p h⟩
  · intro hMB a ha
    obtain ⟨B, E, ρ, J, h⟩ :=
      hMB (spatialMean a) (spatialCurl a) (laws.curl_data a ha)
    have hNS := ns_of_maxwell laws ν c (spatialMean a) (spatialCurl a) B E ρ J h
    rw [laws.reconstruct_velocity a ha] at hNS
    exact ⟨canonicalVelocity (spatialMean a) B,
      canonicalPressureTrajectory ν (spatialMean a) B, hNS⟩

/-- Exact quantifier prefix; the analytic-law premise remains explicit. -/
theorem exact_equivalence_of_periodicAnalyticLaws
    (laws : PeriodicAnalyticLaws) : ExactEquivalence := by
  intro ν hν c hc
  exact feffermanB_iff_maxwellB_of_periodicAnalyticLaws laws ν c

end

end NSEMaxwell.Bridge
