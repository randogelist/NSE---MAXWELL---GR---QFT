import FourierHodgeLaws.SpatialInhabitant
import FourierHodgeLaws.CanonicalInhabitant

/-!
Deterministic exact-target assembly from the actual Fourier integral operators.
Certification requires matching external compilation and theorem-level audits.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Bridge

noncomputable section

theorem fourierHodgeLaws_of_parameter_smoothing
    (hVL : ∀ (B : Velocity), SmoothVelocity B → PeriodicVelocity B →
      SmoothVelocity (fun t => vectorL (B t)))
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t))) : FourierHodgeLaws where
  reconstruct_velocity := h1_reconstruct_velocity
  reconstruct_curl := h2_reconstruct_curl
  canonical_smoothness := H3_of_parameter_smoothing hVL hSL
  electric_hodge := h4_electric_hodge

theorem exact_equivalence_of_parameter_smoothing
    (hVL : ∀ (B : Velocity), SmoothVelocity B → PeriodicVelocity B →
      SmoothVelocity (fun t => vectorL (B t)))
    (hSL : ∀ (f : Pressure), SmoothPressure f → PeriodicPressure f →
      SmoothPressure (fun t => scalarL (f t))) : ExactEquivalence :=
  exact_equivalence_of_fourierHodgeLaws
    (fourierHodgeLaws_of_parameter_smoothing hVL hSL)

theorem fourierHodgeLaws_inhabitant : FourierHodgeLaws where
  reconstruct_velocity := h1_reconstruct_velocity
  reconstruct_curl := h2_reconstruct_curl
  canonical_smoothness := h3_canonical_smoothness
  electric_hodge := h4_electric_hodge

theorem exact_equivalence_native : ExactEquivalence :=
  exact_equivalence_of_fourierHodgeLaws fourierHodgeLaws_inhabitant

end

end NSEMaxwell.HodgeProof
