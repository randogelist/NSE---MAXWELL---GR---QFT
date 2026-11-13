import NSEGRForward

/-!
The reverse implication uses the actual reconstructed fields. The final
quotient assembly separately lists all unresolved gauge and inverse laws.
-/
set_option autoImplicit false

namespace NSEGR
noncomputable section

def reverseRepresentative {ν ρ t0 : ℝ} (h : GeometricReconstructionLaws ν ρ t0)
    (g : CanonicalRepresentative ν ρ t0) : NSERepresentative ν t0 where
  radius := g.timeRadius
  velocity := boundaryVelocity (boundaryK g.metric)
  pressure := boundaryPressure ρ (boundaryK g.metric)
  solution := localNSE_of_reconstruction_and_zero_stress h g.geometry g.stress_zero

theorem GR_TO_NSE_OF_GEOMETRIC_RECONSTRUCTION
    (ν ρ t0 : ℝ) (_hν : 0 < ν) (_hρ : ρ ≠ 0)
    (h : GeometricReconstructionLaws ν ρ t0) (g : CanonicalRepresentative ν ρ t0) :
    LocalNSE ν t0 g.timeRadius (boundaryVelocity (boundaryK g.metric))
      (boundaryPressure ρ (boundaryK g.metric)) :=
  (reverseRepresentative h g).solution

/-- Gauge descent and analytic uniqueness are exact remaining proof obligations.
This record has no supplied inhabitant. A standard-only axiom audit of the
assembly below does not discharge any of these four fields. -/
structure GermInverseLaws {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) : Prop where
  forward_respects : ∀ a b : NSERepresentative ν t0,
    SameFlowAt t0 a.velocity a.pressure b.velocity b.pressure →
      SameMetricAt t0 (forwardRepresentative c r a).metric (forwardRepresentative c r b).metric
  reverse_respects : ∀ a b : CanonicalRepresentative ν ρ t0,
    SameMetricAt t0 a.metric b.metric →
      SameFlowAt t0 (reverseRepresentative h a).velocity (reverseRepresentative h a).pressure
        (reverseRepresentative h b).velocity (reverseRepresentative h b).pressure
  decode_lift : ∀ a : NSERepresentative ν t0,
    SameFlowAt t0 (reverseRepresentative h (forwardRepresentative c r a)).velocity
      (reverseRepresentative h (forwardRepresentative c r a)).pressure a.velocity a.pressure
  lift_decode : ∀ a : CanonicalRepresentative ν ρ t0,
    SameMetricAt t0 (forwardRepresentative c r (reverseRepresentative h a)).metric a.metric

def forwardGerm {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) (q : GermInverseLaws c r h) :
    NSEgerm ν t0 → GRgerm ν ρ t0 :=
  Quotient.map (forwardRepresentative c r) (by
    intro a b hab
    exact q.forward_respects a b hab)

def reverseGerm {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) (q : GermInverseLaws c r h) :
    GRgerm ν ρ t0 → NSEgerm ν t0 :=
  Quotient.map (reverseRepresentative h) (by
    intro a b hab
    exact q.reverse_respects a b hab)

theorem reverseGerm_forwardGerm {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) (q : GermInverseLaws c r h)
    (x : NSEgerm ν t0) : reverseGerm c r h q (forwardGerm c r h q x) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  change NSEgerm.mk (reverseRepresentative h (forwardRepresentative c r a)) = NSEgerm.mk a
  exact NSEgerm.sound (q.decode_lift a)

theorem forwardGerm_reverseGerm {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) (q : GermInverseLaws c r h)
    (x : GRgerm ν ρ t0) : forwardGerm c r h q (reverseGerm c r h q x) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  change GRgerm.mk (forwardRepresentative c r (reverseRepresentative h a)) = GRgerm.mk a
  exact GRgerm.sound (q.lift_decode a)

def exactSectorEquivOfContracts {ν ρ t0 : ℝ}
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) (q : GermInverseLaws c r h) :
    NSEgerm ν t0 ≃ GRgerm ν ρ t0 where
  toFun := forwardGerm c r h q
  invFun := reverseGerm c r h q
  left_inv := reverseGerm_forwardGerm c r h q
  right_inv := forwardGerm_reverseGerm c r h q

theorem NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_NAMED_CONTRACTS
    (ν ρ t0 : ℝ) (_hν : 0 < ν) (_hρ : ρ ≠ 0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0) (r : AnalyticRadialExtensionLaws ρ t0)
    (h : GeometricReconstructionLaws ν ρ t0) (q : GermInverseLaws c r h) :
    ExactSectorEquivalence ν ρ t0 :=
  ⟨exactSectorEquivOfContracts c r h q⟩

end
end NSEGR
