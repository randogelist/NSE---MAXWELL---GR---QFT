import GRAdapter.Germs
import GRAdapter.CompletionSource

/-!
# Named remaining analytic and geometric obligations

The fields below refer to actual analytic functions, coordinate derivatives,
the concrete Einstein tensor, and the independently defined normalized sector.
No inhabitant is asserted. Their presence in a theorem is a remaining premise.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace NSEGR
noncomputable section

/-- A concrete normalized scalar completion and its resulting constrained jet. -/
structure CompletedBoundary (ν ρ t0 : ℝ) (n : NSERepresentative ν t0) where
  timeRadius : ℝ
  radius_le_source : timeRadius ≤ n.radius
  potential : Pressure
  potential_analytic : AnalyticOnNhd ℝ (fun z : ℝ × Vec => potential z.1 z.2)
    (spacetimeSlab t0 timeRadius)
  potential_periodic : ∀ t ∈ timeInterval t0 timeRadius, SpatialPeriodic (potential t)
  potential_initial : ∀ x, potential t0 x = 0
  potential_time_initial : ∀ x, scalarLocalTimeDerivative potential t0 x = 0
  tensor : BoundaryTensor
  tensor_eq : tensor = completedBoundary ν ρ n.velocity n.pressure potential
  admissible : BoundaryAdmissible ρ t0 timeRadius tensor
  stress_zero : ∀ t ∈ timeInterval t0 timeRadius, ∀ x, boundaryStress ν tensor t x = 0
  velocity_recovery : ∀ t ∈ timeInterval t0 timeRadius,
    boundaryVelocity tensor t = n.velocity t
  pressure_recovery : SameFlowAt t0 (boundaryVelocity tensor) (boundaryPressure ρ tensor)
    n.velocity n.pressure

/-- Scalar CK, its actual constraints, and the concrete boundary reconstruction.
The noncharacteristic rho condition is an explicit argument of the final roots. -/
structure ScalarBoundaryCompletionLaws (ν ρ t0 : ℝ) : Prop where
  complete : ∀ n : NSERepresentative ν t0, Nonempty (CompletedBoundary ν ρ t0 n)

/-- An actual analytic radial vacuum extension on a possibly smaller time collar. -/
structure RadialExtensionResult (ρ t0 δ : ℝ) (K : BoundaryTensor) where
  timeRadius : ℝ
  time_radius_le : timeRadius ≤ δ
  radialRadius : ℝ
  metric : Metric
  geometry : GaussianVacuum ρ t0 timeRadius radialRadius metric
  boundary_match : ∀ t ∈ timeInterval t0 timeRadius, boundaryK metric t = K t

/-- Radial CK and constraint propagation for an independently constrained tensor. -/
structure AnalyticRadialExtensionLaws (ρ t0 : ℝ) : Prop where
  extend : ∀ (δ : ℝ) (K : BoundaryTensor), BoundaryAdmissible ρ t0 δ K →
    Nonempty (RadialExtensionResult ρ t0 δ K)

/-- Actual Gauss--Codazzi, analytic torus reconstruction, and the residual identity.
These fields have not been replaced by an abstract solution proposition. -/
structure GeometricReconstructionLaws (ν ρ t0 : ℝ) : Prop where
  regularity : ∀ (δ ε : ℝ) (g : Metric), GaussianVacuum ρ t0 δ ε g →
    AnalyticPeriodicPair t0 δ (boundaryVelocity (boundaryK g))
      (boundaryPressure ρ (boundaryK g))
  solenoidal : ∀ (δ ε : ℝ) (g : Metric), GaussianVacuum ρ t0 δ ε g →
    ∀ t ∈ timeInterval t0 δ, ∀ x, divergence (boundaryVelocity (boundaryK g) t) x = 0
  residual : ∀ (δ ε : ℝ) (g : Metric), GaussianVacuum ρ t0 δ ε g →
    ∀ t ∈ timeInterval t0 δ, ∀ x,
      nseResidual ν (boundaryVelocity (boundaryK g)) (boundaryPressure ρ (boundaryK g)) t x =
        tensorDivergence (boundaryStress ν (boundaryK g) t) x

/-- This implication uses the exact zero tensor as a function of all spatial points. -/
theorem localNSE_of_reconstruction_and_zero_stress
    {ν ρ t0 δ ε : ℝ} {g : Metric}
    (laws : GeometricReconstructionLaws ν ρ t0)
    (hg : GaussianVacuum ρ t0 δ ε g)
    (hF : ∀ t ∈ timeInterval t0 δ, ∀ x, boundaryStress ν (boundaryK g) t x = 0) :
    LocalNSE ν t0 δ (boundaryVelocity (boundaryK g)) (boundaryPressure ρ (boundaryK g)) := by
  refine { toAnalyticPeriodicPair := laws.regularity δ ε g hg
           divergence_free := laws.solenoidal δ ε g hg
           momentum := ?_ }
  intro t ht x
  rw [laws.residual δ ε g hg t ht x]
  have hzero : boundaryStress ν (boundaryK g) t = (fun _ : Vec => (0 : Tensor3)) :=
    funext (hF t ht)
  rw [hzero]
  exact congrFun (tensorDivergence_const (0 : Tensor3)) x

theorem timeInterval_mono {t0 δ η : ℝ} (h : δ ≤ η) :
    timeInterval t0 δ ⊆ timeInterval t0 η := by
  intro t ht
  change t0 - δ < t ∧ t < t0 + δ at ht
  change t0 - η < t ∧ t < t0 + η
  constructor <;> linarith [ht.1, ht.2]

theorem timeInterval_mem_nhds (t0 δ : ℝ) (hδ : 0 < δ) :
    timeInterval t0 δ ∈ 𝓝 t0 := by
  apply Ioo_mem_nhds <;> linarith

/-- Exact independently defined carrier-level root; no existence premise is hidden. -/
def ExactSectorEquivalence (ν ρ t0 : ℝ) : Prop :=
  Nonempty (NSEgerm ν t0 ≃ GRgerm ν ρ t0)

end
end NSEGR
