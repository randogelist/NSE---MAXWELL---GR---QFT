import ClassicalMechanicsAssembly.FlowRealization
import ClassicalMechanicsAssembly.FlowGlobalSlab
import ClassicalMechanicsAssembly.FlowMaterialCoherence
import ClassicalMechanicsAssembly.FlowMaterialFields
import ClassicalMechanics.Equivalence

/-!
# Global NSE-B and material classical mechanics

`CMSolution` retains the global smooth incompressible kinematics and initial
datum, and imposes momentum balance only in actual material coordinates on
every positive closed slab. A single pair `(u,p)` precedes the slab quantifier.
No Eulerian momentum equation, supplied flow, or literature input is a field.
Slab flows are coherent by ODE uniqueness. Pressure keeps its arbitrary gauge.
This endpoint is separate from the normalized `MaterialSolutionOn` predicate
and from a moving-region or Lagrange-d'Alembert variational formulation.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- Global incompressible kinematics with literal material momentum equations. -/
structure CMSolution (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : SmoothVelocity u
  pressure_smooth : SmoothPressure p
  velocity_periodic : PeriodicVelocity u
  pressure_periodic : PeriodicPressure p
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0
  initial : u 0 = a
  material : ∀ T : ℝ, 0 < T → ∃ η ρ : Velocity,
    MaterialPathOn T η ρ ∧
    (∀ t ∈ Icc (0 : ℝ) T, ∀ b : Vec,
      materialVelocity T η t b = u t (η t b)) ∧
    MaterialEquationOn ν T η (fun t b => p t (η t b))

/-- Classical-mechanics existence with the same data and global quantifiers as NSE-B. -/
def CMB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a → ∃ u : Velocity, ∃ p : Pressure, CMSolution ν a u p

/-- Forward edge: native L1 and Piola transport construct each material chart. -/
theorem nseSolution_to_cmSolution {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolution ν a u p) : CMSolution ν a u p := by
  refine ⟨h.velocity_smooth, h.pressure_smooth, h.velocity_periodic,
    h.pressure_periodic, h.divergence_free, h.initial, ?_⟩
  intro T hT
  have hu := global_smoothVelocityOn h.velocity_smooth T
  have hp := global_smoothPressureOn h.pressure_smooth T
  obtain ⟨η, ρ, hη, hflow⟩ := L1_native hT hu
    (fun t ht => h.velocity_periodic t ht.1)
    (fun t ht x => h.divergence_free t ht.1 x)
  refine ⟨η, ρ, hη, hflow, ?_⟩
  exact eulerian_equation_implies_material_of_flow hT hu hp hη hflow
    (global_equation_to_finite_equation hT h.velocity_smooth h.equation)

/-- Reverse edge: each actual chart supplies momentum balance on its entire slab. -/
theorem cmSolution_to_nseSolution {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : CMSolution ν a u p) : NSSolution ν a u p := by
  refine ⟨h.velocity_smooth, h.pressure_smooth, h.velocity_periodic,
    h.pressure_periodic, h.divergence_free, ?_, h.initial⟩
  apply finite_equations_to_global_equation h.velocity_smooth
  intro T hT
  obtain ⟨η, ρ, hη, hflow, hM⟩ := h.material T hT
  exact material_equation_implies_eulerian_of_flow hT
    (global_smoothVelocityOn h.velocity_smooth T)
    (global_smoothPressureOn h.pressure_smooth T) hη hflow hM

/-- Exact equivalence over the same global velocity and pressure. -/
theorem nseSolution_iff_cmSolution {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure} :
    NSSolution ν a u p ↔ CMSolution ν a u p :=
  ⟨nseSolution_to_cmSolution, cmSolution_to_nseSolution⟩

/-- Equality of solution predicates projected to their common global fields. -/
theorem nse_cm_solution_sets_eq (ν : ℝ) (a : Field) :
    {s : Velocity × Pressure | NSSolution ν a s.1 s.2} =
      {s : Velocity × Pressure | CMSolution ν a s.1 s.2} := by
  ext s
  exact nseSolution_iff_cmSolution

theorem nseB_implies_cmB (ν : ℝ) (h : FeffermanB ν) : CMB ν := by
  intro a ha
  obtain ⟨u, p, hs⟩ := h a ha
  exact ⟨u, p, nseSolution_to_cmSolution hs⟩

theorem cmB_implies_nseB (ν : ℝ) (h : CMB ν) : FeffermanB ν := by
  intro a ha
  obtain ⟨u, p, hs⟩ := h a ha
  exact ⟨u, p, cmSolution_to_nseSolution hs⟩

/-- Exact requested existence equivalence; no analytic premises remain. -/
theorem NSEB_IFF_CM (ν : ℝ) : FeffermanB ν ↔ CMB ν :=
  ⟨nseB_implies_cmB ν, cmB_implies_nseB ν⟩

/-- Positive-viscosity specialization to the original NSE-B problem. -/
theorem NSEB_IFF_CM_POSITIVE : ∀ ν : ℝ, 0 < ν → (FeffermanB ν ↔ CMB ν) := by
  intro ν _hν
  exact NSEB_IFF_CM ν

/-- Local Newtonian Cauchy balance and material classical mechanics have the same scope. -/
theorem newtonianB_iff_cmB (ν : ℝ) : NewtonianB ν ↔ CMB ν :=
  (feffermanB_iff_newtonianB ν).symm.trans (NSEB_IFF_CM ν)

end

end ClassicalMechanicsAssembly
