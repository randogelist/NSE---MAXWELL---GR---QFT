import NSEMaxwell.Negation
import NSEMaxwell.Lamb
import NSEMaxwell.Pressure

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

/-- Smooth divergence-free mean-zero magnetic trajectories, including t = 0. -/
structure MagneticPath (B : Velocity) : Prop where
  smooth : SmoothVelocity B
  periodic : PeriodicVelocity B
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (B t) x = 0
  mean_zero : ∀ t : ℝ, 0 ≤ t → spatialMean (B t) = 0

theorem MagneticPath.slice {B : Velocity} (h : MagneticPath B)
    {t : ℝ} (ht : 0 ≤ t) : MagneticData (B t) := by
  exact ⟨⟨velocity_slice_smooth h.smooth ht, h.periodic t ht,
    h.divergence_free t ht⟩, h.mean_zero t ht⟩

def curlTrajectory (u : Velocity) : Velocity := fun t => spatialCurl (u t)

def momentumResidual (ν : ℝ) (u : Velocity) (p : Pressure) (t : ℝ) : Field :=
  timeDerivative u t + convection (u t) + gradient (p t) - ν • laplacian (u t)

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
    divergence (canonicalVelocity m B t) x = 0

/--
OPEN ANALYTIC PREMISES. Each field is a concrete analytic statement, not a new
axiom declaration. An unconditional root theorem requires a proved inhabitant
of this structure. No such inhabitant is asserted in this repository.
-/
structure PeriodicAnalyticLaws : Prop where
  curl_data : ∀ (a : Field), Data a → MagneticData (spatialCurl a)
  reconstruction_data : ∀ (m : Vec) (B : Field), MagneticData B → Data (U m B)
  reconstruct_velocity : ∀ (a : Field), Data a →
    U (spatialMean a) (spatialCurl a) = a
  reconstruct_curl : ∀ (m : Vec) (B : Field), MagneticData B →
    spatialCurl (U m B) = B
  reconstruct_mean : ∀ (m : Vec) (B : Field), MagneticData B →
    spatialMean (U m B) = m
  vorticity_regularity : ∀ (u : Velocity),
    SmoothVelocity u → PeriodicVelocity u →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0) →
    MagneticPath (curlTrajectory u)
  canonical_regularity : ∀ (ν c : ℝ) (m : Vec) (B : Velocity),
    MagneticPath B → CanonicalRegularity ν c m B
  mean_conservation : ∀ (ν : ℝ) (u : Velocity) (p : Pressure),
    SmoothVelocity u → SmoothPressure p →
    PeriodicVelocity u → PeriodicPressure p →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0) →
    (∀ t : ℝ, 0 ≤ t → momentumResidual ν u p t = 0) →
    ∀ t : ℝ, 0 ≤ t → spatialMean (u t) = spatialMean (u 0)
  vorticity_residual : ∀ (ν : ℝ) (u : Velocity) (p : Pressure),
    SmoothVelocity u → SmoothPressure p →
    PeriodicVelocity u → PeriodicPressure p →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0) →
    ∀ t : ℝ, 0 ≤ t →
    spatialCurl (momentumResidual ν u p t) =
      timeDerivative (curlTrajectory u) t +
        spatialCurl (fun x => cross (spatialCurl (u t) x) (u t x) +
          ν • spatialCurl (spatialCurl (u t)) x)
  reconstruction_time : ∀ (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    timeDerivative (canonicalVelocity m B) t = K (timeDerivative B t)
  viscosity_identity : ∀ (ν : ℝ) (m : Vec) (B : Field), MagneticData B →
    ν • laplacian (U m B) = -(ν • spatialCurl B)
  electric_hodge : ∀ (ν : ℝ) (m : Vec) (B : Field), MagneticData B →
    G ν m B + gradient (headPotential ν m B) = K (spatialCurl (G ν m B))
  K_residual_add : ∀ (ν : ℝ) (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    K (timeDerivative B t + spatialCurl (G ν m (B t))) =
      K (timeDerivative B t) + K (spatialCurl (G ν m (B t)))
  electric_time_chain : ∀ (ν : ℝ) (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    timeDerivative (canonicalElectric ν m B) t =
      DG ν m (B t) (timeDerivative B t)
  DG_residual_add : ∀ (ν : ℝ) (m : Vec) (B : Velocity), MagneticPath B →
    ∀ t : ℝ, 0 ≤ t →
    DG ν m (B t) (timeDerivative B t + spatialCurl (G ν m (B t))) =
      DG ν m (B t) (timeDerivative B t) +
        DG ν m (B t) (spatialCurl (G ν m (B t)))

theorem momentum_zero_of_ns {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolution ν a u p) (t : ℝ) (ht : 0 ≤ t) :
    momentumResidual ν u p t = 0 := by
  funext x
  exact sub_eq_zero.mpr (h.equation t ht x)

/-- The concrete momentum factorization, derived from the named primitive laws. -/
theorem canonical_momentum_factorization
    (laws : PeriodicAnalyticLaws) (ν : ℝ) (m : Vec) (B : Velocity)
    (hB : MagneticPath B) (t : ℝ) (ht : 0 ≤ t) :
    momentumResidual ν (canonicalVelocity m B)
        (canonicalPressureTrajectory ν m B) t =
      K (faradayResidual ν m B t) := by
  have hs := hB.slice ht
  have hG : G ν m (B t) = lambField m (B t) + ν • spatialCurl (B t) := rfl
  have hLamb : convection (U m (B t)) =
      lambField m (B t) + gradient (kineticPotential m (B t)) :=
    NSEMaxwell.Lamb.reconstructed_lamb_identity m (B t)
      (laws.reconstruction_data m (B t) hs) (laws.reconstruct_curl m (B t) hs)
  have hReg := laws.canonical_regularity ν 0 m B hB
  have hPressure : gradient (canonicalPressure ν m (B t)) =
      gradient (headPotential ν m (B t)) - gradient (kineticPotential m (B t)) :=
    canonicalPressure_gradient ν m (B t)
      (velocity_slice_smooth hReg.velocity_smooth ht)
      (pressure_slice_smooth hReg.pressure_smooth ht)
  change timeDerivative (canonicalVelocity m B) t + convection (U m (B t)) +
      gradient (canonicalPressure ν m (B t)) - ν • laplacian (U m (B t)) = _
  rw [laws.reconstruction_time m B hB t ht, hLamb,
    hPressure, laws.viscosity_identity ν m (B t) hs]
  calc
    K (timeDerivative B t) +
        (lambField m (B t) + gradient (kineticPotential m (B t))) +
        (gradient (headPotential ν m (B t)) - gradient (kineticPotential m (B t))) -
        -(ν • spatialCurl (B t)) =
      K (timeDerivative B t) +
        (G ν m (B t) + gradient (headPotential ν m (B t))) := by rw [hG]; abel
    _ = K (timeDerivative B t) + K (spatialCurl (G ν m (B t))) := by
      rw [laws.electric_hodge ν m (B t) hs]
    _ = K (faradayResidual ν m B t) :=
      (laws.K_residual_add ν m B hB t ht).symm

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
    exact ampere_zero_of_faraday ν c m B t
      (laws.electric_time_chain ν m B hB t ht)
      (laws.DG_residual_add ν m B hB t ht)
      (DG_curl_neg ν m (B t))
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
      rw [canonical_momentum_factorization laws ν m B hB t ht,
        canonical_faraday_of_maxwell ν c m B₀ B E ρ J h t ht, K_zero]
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
