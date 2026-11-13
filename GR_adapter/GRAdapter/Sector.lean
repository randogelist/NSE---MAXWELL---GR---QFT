import GRAdapter.Boundary

/-!
# Independent constrained boundary and normalized marked vacuum sectors

The metric predicate refers to actual Lorentzian curvature, Gaussian gauge,
boundary jets and normalization. It is not the image of a lift, and does not
contain an NSE solution predicate. The vacuum-to-constraint theorem and the
analytic radial extension theorem remain independent formal obligations.
-/

set_option autoImplicit false

open Set

namespace NSEGR

noncomputable section

/-- Flat-boundary constraints, defined independently of a bulk metric. -/
structure BoundaryAdmissible (ρ t0 δ : ℝ) (K : BoundaryTensor) : Prop where
  radius_pos : 0 < δ
  analytic : AnalyticOnNhd ℝ (fun z : ℝ × Vec => K z.1 z.2) (spacetimeSlab t0 δ)
  periodic : ∀ t ∈ timeInterval t0 δ, SpatialPeriodic (K t)
  symmetric : ∀ t ∈ timeInterval t0 δ, ∀ x, (K t x).IsSymm
  momentum_constraint : ∀ t ∈ timeInterval t0 δ, ∀ x b, boundaryCodazzi K t x b = 0
  hamiltonian : ∀ t ∈ timeInterval t0 δ, ∀ x, boundaryHamiltonian K t x = 0
  beta_initial : ∀ x, boundaryBeta K t0 x = ρ
  beta_time_initial : ∀ x, deriv (fun t : ℝ => boundaryBeta K t x) t0 = 0

def bulkCollar (t0 δ ε : ℝ) : Set Bulk :=
  {z | z 0 ∈ Ioo (-ε) ε ∧ z 1 ∈ timeInterval t0 δ}

/-- The ambient actual marked analytic normalized vacuum predicate. -/
structure GaussianVacuum (ρ t0 δ ε : ℝ) (g : Metric) : Prop where
  time_radius_pos : 0 < δ
  radial_radius_pos : 0 < ε
  analytic : AnalyticOnNhd ℝ g (bulkCollar t0 δ ε)
  periodic : ∀ r ∈ Ioo (-ε) ε, ∀ t ∈ timeInterval t0 δ,
    SpatialPeriodic (fun x => g (bulkPoint r t x))
  symmetric : ∀ z ∈ bulkCollar t0 δ ε, (g z).IsSymm
  lorentzian : ∀ z ∈ bulkCollar t0 δ ε, LorentzianAt g z
  gaussian_rr : ∀ z ∈ bulkCollar t0 δ ε, g z 0 0 = 1
  gaussian_rboundary : ∀ z ∈ bulkCollar t0 δ ε, ∀ a : Fin 4,
    g z 0 (boundaryIndex a) = 0
  induced : ∀ t ∈ timeInterval t0 δ, ∀ x a b,
    g (bulkPoint 0 t x) (boundaryIndex a) (boundaryIndex b) = eta4 a b
  vacuum : VacuumOn g (bulkCollar t0 δ ε)
  beta_initial : ∀ x, boundaryBeta (boundaryK g) t0 x = ρ
  beta_time_initial : ∀ x,
    deriv (fun t : ℝ => boundaryBeta (boundaryK g) t x) t0 = 0

structure VacuumRepresentative (ρ t0 : ℝ) where
  timeRadius : ℝ
  radialRadius : ℝ
  metric : Metric
  geometry : GaussianVacuum ρ t0 timeRadius radialRadius metric

/-- Constitutive admission is computed solely from the actual marked metric jet. -/
structure CanonicalRepresentative (ν ρ t0 : ℝ) where
  timeRadius : ℝ
  radialRadius : ℝ
  metric : Metric
  geometry : GaussianVacuum ρ t0 timeRadius radialRadius metric
  stress_zero : ∀ t ∈ timeInterval t0 timeRadius, ∀ x,
    boundaryStress ν (boundaryK metric) t x = 0

def CanonicalRepresentative.toVacuum {ν ρ t0 : ℝ}
    (g : CanonicalRepresentative ν ρ t0) : VacuumRepresentative ρ t0 where
  timeRadius := g.timeRadius
  radialRadius := g.radialRadius
  metric := g.metric
  geometry := g.geometry

theorem canonical_stress_trace_zero {ν ρ t0 : ℝ}
    (g : CanonicalRepresentative ν ρ t0) (t : ℝ) (x : Vec) :
    trace3 (boundaryStress ν (boundaryK g.metric) t x) = 0 :=
  boundaryStress_trace_zero ν (boundaryK g.metric) t x

theorem gaussianVacuum_nondegenerate {ρ t0 δ ε : ℝ} {g : Metric}
    (h : GaussianVacuum ρ t0 δ ε g) (z : Bulk) (hz : z ∈ bulkCollar t0 δ ε) :
    (g z).det ≠ 0 :=
  lorentzianAt_nondegenerate (h.lorentzian z hz)

theorem gaussianVacuum_einstein {ρ t0 δ ε : ℝ} {g : Metric}
    (h : GaussianVacuum ρ t0 δ ε g) : EinsteinVacuumOn g (bulkCollar t0 δ ε) :=
  vacuumOn_implies_einsteinVacuumOn h.vacuum

/-- The zero boundary is an actual constrained boundary, at rho=0 only. -/
theorem boundaryAdmissible_zero (t0 δ : ℝ) (hδ : 0 < δ) :
    BoundaryAdmissible 0 t0 δ (0 : BoundaryTensor) where
  radius_pos := hδ
  analytic := analyticOnNhd_const
  periodic := by intro t ht; exact spatialPeriodic_const 0
  symmetric := by intro t ht x; exact Matrix.isSymm_zero
  momentum_constraint := by intro t ht x b; simp
  hamiltonian := by intro t ht x; simp
  beta_initial := by intro x; simp
  beta_time_initial := by intro x; simp

/-- Flat vacuum by itself does not meet the original nonzero-rho normalization. -/
theorem flatMetric_not_gaussianVacuum (ρ t0 δ ε : ℝ) (hρ : ρ ≠ 0) :
    ¬ GaussianVacuum ρ t0 δ ε flatMetric := by
  intro h
  have hzero : (0 : ℝ) = ρ := by
    simpa using h.beta_initial (0 : Vec)
  exact hρ hzero.symm

theorem boundaryAdmissible_zero_parameter {ρ t0 δ : ℝ}
    (h : BoundaryAdmissible ρ t0 δ (0 : BoundaryTensor)) : ρ = 0 := by
  have hzero : (0 : ℝ) = ρ := by
    simpa using h.beta_initial (0 : Vec)
  exact hzero.symm

end

end NSEGR
